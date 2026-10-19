#!/usr/bin/env python3
"""
navigate_generic.py
----------------------------
Generic, phase-based app exploration - meant to work on ANY webview-based
APK without per-app tuning. This replaces the keyword/priority-driven
navigation in navigate_full_explore.py with a simpler idea: click every
clickable thing on the screen (not just text-labeled ones, and not
filtered/reordered by what the label SAYS), fully explore wherever it
leads, then come back and move on to the next one.

Why this version exists (the previous script's real limitation):
Some apps hide Deposit/Withdraw behind a hamburger (<SVG> icon, no text)
or a profile avatar (<IMG>, no text). The previous element-finder only
picked up elements that had visible text, so those icons were invisible
to it - the script never even considered tapping them, no matter how the
priority keywords were tuned. This version fixes that at the source: the
element finder now also catches icon-only clickable elements.

The ONLY thing that stays keyword-based is the real-money safety
boundary (never tap into an actual casino game, never place a live bet,
never tap logout/uninstall/external-link/login elements). That boundary
is a hard safety rule, not a navigation strategy, so it is kept separate
from everything else and is never relaxed.

Hard guarantee: this script only ever sends Android BACK (keyevent 4).
It never sends HOME (3) or APP_SWITCH/RECENTS (187), and it checks the
actual current screen before every Back press so it can't walk the app
closed by pressing Back once too often from Home.

Usage:
    python3 navigate_generic.py <package_name> [--max-depth N]
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

import websocket

# =============================================================================
# PHASE 0 config - connection, scale, output
# =============================================================================
LOCAL_CDP_PORT = 9222
OUTPUT_DIR = Path("nav_captures")
TAP_LOG_PATH = OUTPUT_DIR / "tap_log.csv"
MAX_DEPTH_DEFAULT = 6
TARGET_AMOUNT = "100"
AMOUNT_FIELD_HINTS = ["amount", "enter amount"]
SUBMIT_KEYWORDS = ["submit", "confirm", "proceed", "pay now", "continue", "next"]
PER_SCREEN_ELEMENT_LIMIT = 30
SCREEN_SETTLE_TIMEOUT = 6
SCREEN_SETTLE_POLL = 0.4

# =============================================================================
# PHASE 2 config - the ONLY keyword-driven part: the safety boundary.
# Never reordered, never skipped, never tuned per-app. Everything else in
# this script is generic (click-everything), this part alone stays as an
# explicit blocklist because it's a safety requirement, not a strategy.
# =============================================================================
BLOCK_PAT = re.compile(
    r"(log\s*in|sign\s*in|sign\s*up|register|create\s*account|continue\s*with|google|apple|facebook|microsoft|sso"
    r"|http[s]?://|privacy policy|terms of service|open in browser|rate|store|share|maps?"
    r"|back|exit|close|cancel|logout|log out|sign out|delete|remove|uninstall|quit"
    r"|casino provider|live casino|slots?|roulette|blackjack|poker|baccarat"
    r"|diamond|evolution|betsoft|ezugi|gamzix|betgames|spin|jackpot|bet now|play now"
    r"|live stream|^match$|place bet|place stake|cricket|football|tennis|kabaddi"
    r"|basketball|baseball|greyhound|horse race|volleyball|darts|futsal|table tennis"
    r"|ice hockey|mma|rugby|mini games|fantasy)",
    re.I,
)

# Structural exclusion - catches the SHAPE of volatile content (live odds,
# times, dates) regardless of wording, since these rows are often
# identified only by a number/time with no sport-name keyword present.
VOLATILE_PAT = re.compile(
    r"^\d{1,2}:\d{2}\s*(AM|PM)?$"
    r"|^\d{1,2}\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)$"
    r"|^\d+\.\d+$"
    r"|^\d+K$"
    r"|^(Today|Tomorrow)$",
    re.I,
)

REDIRECT_METHOD_KEYWORDS = ["whatsapp", "telegram", "contact support", "chat with", "channel"]

# Confirmed via a real run (bdgwin04.com's Home screen, co.median.android.
# abzjprp): a row of casino slot-provider logos (JILI, PG, CQ9, MG, JDB,
# AG_Electronic, EVO_Electronic, G9, MG_Fish) sits directly under the
# AllOnlineGames route and would launch an actual slot game if tapped -
# these were harmless in that run only because a separate bug (see
# viewport-bounds check below) happened to make them untappable. Blocked
# here explicitly rather than relying on that accident. Matched as a
# WHOLE label (not a substring) so short codes like "MG" don't
# accidentally blow away unrelated text elsewhere that merely contains
# those letters.
GAME_PROVIDER_PAT = re.compile(
    r"^(jili|pg|pg\s*soft|cq9|mg|jdb|ag[_\s]?electronic|evo[_\s]?electronic|g9|mg[_\s]?fish"
    r"|pp|fc|wm|sa|dg|ab|joker|pragmatic(\s*play)?|playtech|habanero|netent|microgaming"
    r"|spadegaming|kiss918|pussy888|live\s*casino|slot\s*games?)$",
    re.I,
)


def is_excluded(text):
    """The keyword-based checks left in this script - the safety
    boundary. Everything else in the script treats the screen
    generically; only this function is allowed to say "never tap this",
    and it covers two things: the general BLOCK_PAT/VOLATILE_PAT safety
    list, and specifically-identified game-provider logos."""
    stripped = text.strip()
    return (
        bool(BLOCK_PAT.search(text))
        or bool(VOLATILE_PAT.match(stripped))
        or bool(GAME_PROVIDER_PAT.match(stripped))
    )


# Matches an in-app "back" control: a literal arrow glyph, or a label/
# class name identifying it as a back button. Checked FIRST, before ever
# sending a hardware Back key press - see navigate_to_hash() below.
BACK_BUTTON_PAT = re.compile(
    r"^[<‹←⟨«]$"                          # literal glyphs: < ‹ ← ⟨ «
    r"|\bback\b|\barrow[-_\s]?left\b|\bchevron[-_\s]?left\b|\bnav[-_\s]?back\b|\bgo\s*back\b",
    re.I,
)


def find_in_app_back_button(elements):
    """Looks for the app's OWN on-screen back control. These apps are
    hash-routed single-page apps - Android's hardware Back key often has
    no real entry to pop and can just close the Activity, which is
    exactly the accidental-exit problem this project has been fighting.
    The app's own "<" is the way the app actually expects to be
    navigated backward, so it's tried first; the hardware key is only a
    fallback for screens that don't have one."""
    for e in elements:
        t = e.get("text", "")
        if t and BACK_BUTTON_PAT.search(t):
            return e
    return None


def candidate_key(e):
    """Identifies an element for the 'already tapped on this screen' set.
    A labeled element (real text) is keyed by that text alone, same as
    before. An icon-only element - which often has no aria-label and so
    falls back to a generic name like "(icon: svg)" - is keyed by that
    label PLUS its rounded position. Confirmed via a real run: two
    different icon buttons (a menu icon and, separately, the Wallet
    icon) both fell back to the same generic "(icon: svg)"/"(icon: use)"
    label with no position in the key, so the second one was wrongly
    treated as a repeat of the first and silently skipped - Wallet was
    never actually missing, it was being mistaken for an icon already
    tapped elsewhere on the screen."""
    if e.get("is_icon_only"):
        return f"{e.get('text')}@{round(e['x'] / 12)},{round(e['y'] / 12)}"
    return e.get("text")


def is_redirect_method_label(text):
    """Checks a button's own label before tapping it - a redirect-type
    method (WhatsApp/Telegram deposit) has no real form behind it, so we
    note it without actually leaving the app to open that chat."""
    return any(kw in text.lower() for kw in REDIRECT_METHOD_KEYWORDS)


# =============================================================================
# PHASE 1 - element discovery, including icon-only clickables
# =============================================================================
# This is the actual fix for the "hidden behind a hamburger/profile icon"
# problem. An icon-only button (an <svg> or <img> inside a <button>, no
# visible text) is now captured too, labeled from aria-label/title/alt
# when there's no text, with de-duplication so a button and the icon
# inside it aren't both counted as separate taps.
FIND_ELEMENTS_JS = """
(function() {
    function isClickable(el) {
        if (!el || !el.tagName) return false;
        const tag = el.tagName;
        if (tag === 'BUTTON' || tag === 'A') return true;
        const role = el.getAttribute && el.getAttribute('role');
        if (role === 'button' || role === 'link' || role === 'menuitem' || role === 'tab') return true;
        if (el.onclick) return true;
        if (el.hasAttribute && el.hasAttribute('onclick')) return true;
        try {
            const style = window.getComputedStyle(el);
            if (style.cursor === 'pointer') return true;
        } catch (e) {}
        return false;
    }

    function nearbyCaptionText(el) {
        // Many of these UIs put an icon and its caption as SIBLINGS
        // inside a shared wrapper (an icon + a separate <span>CQ9</span>
        // next to it), not one nested inside the other. Pulling in a
        // sibling's short caption as the icon's effective label closes a
        // real safety gap (a game-provider logo's own caption text was
        // correctly blocked, but the icon next to it had no text/
        // aria-label of its own and slipped through un-blocked) and
        // gives meaningful icons (Wallet, Home, Activity) a real label
        // instead of a generic one two different icons could collide on.
        //
        // This has to be narrow, though. Confirmed via a real run: an
        // unqualified sibling/cousin scan picked up text from elements
        // that were HIDDEN (e.g. a logged-out-state button sitting in
        // the DOM but never shown) or simply far away in the same row,
        // mislabeling unrelated icons with things like "Login" - which
        // then got them wrongly blocked by the safety list, collapsing
        // an 11-element screen down to a single tappable candidate. A
        // candidate caption only counts if it's actually VISIBLE and
        // physically CLOSE to the icon - not just any DOM sibling.
        const rect = el.getBoundingClientRect();
        const centerX = rect.left + rect.width / 2;
        const centerY = rect.top + rect.height / 2;
        const PROXIMITY_PX = 70;

        function plausibleCaption(candidate) {
            if (candidate === el) return null;
            const crect = candidate.getBoundingClientRect();
            if (crect.width <= 0 || crect.height <= 0) return null;
            const cstyle = window.getComputedStyle(candidate);
            if (cstyle.display === 'none' || cstyle.visibility === 'hidden') return null;
            const t = (candidate.innerText || candidate.textContent || '').trim();
            if (!t || t.length > 30) return null;
            const cCenterX = crect.left + crect.width / 2;
            const cCenterY = crect.top + crect.height / 2;
            const dx = Math.abs(cCenterX - centerX);
            const dy = Math.abs(cCenterY - centerY);
            if (dx > PROXIMITY_PX || dy > PROXIMITY_PX) return null;
            return t;
        }

        const parent = el.parentElement;
        if (!parent) return null;
        for (const sib of parent.children) {
            const t = plausibleCaption(sib);
            if (t) return t;
        }
        const grandparent = parent.parentElement;
        if (grandparent) {
            for (const cousin of grandparent.children) {
                if (cousin === parent) continue;
                const t = plausibleCaption(cousin);
                if (t) return t;
            }
        }
        return null;
    }

    function iconLabel(el) {
        const aria = el.getAttribute && el.getAttribute('aria-label');
        if (aria && aria.trim()) return aria.trim();
        const title = el.getAttribute && el.getAttribute('title');
        if (title && title.trim()) return title.trim();
        if (el.tagName === 'IMG') {
            const alt = el.getAttribute('alt');
            if (alt && alt.trim()) return alt.trim();
        }
        const caption = nearbyCaptionText(el);
        if (caption) return caption;
        const testid = el.getAttribute && (el.getAttribute('data-testid') || el.getAttribute('data-test'));
        if (testid && testid.trim()) return '(icon: ' + testid.trim() + ')';
        const cls = (typeof el.className === 'string') ? el.className : '';
        if (cls.trim()) return '(icon: ' + cls.trim().split(/\\s+/)[0] + ')';
        return '(icon: ' + el.tagName.toLowerCase() + ')';
    }

    const allElements = Array.from(document.querySelectorAll('*'));
    const results = [];

    for (const el of allElements) {
        const text = (el.innerText || el.textContent || '').trim();
        const isInput = el.tagName === 'INPUT' || el.tagName === 'TEXTAREA' || el.isContentEditable;
        const clickable = isClickable(el);

        // Keep this element if it has text, is an input, OR is itself
        // clickable (even with no text - that's the icon-button case).
        if (!text && !isInput && !clickable) continue;
        if (text.length > 60) continue;

        if (text) {
            // Skip a wrapper div whose child already carries this same
            // text (avoid double-counting a card and the label inside
            // it) - but never skip based on this for icon-only elements,
            // they have no text to begin with.
            const childHasOwnText = Array.from(el.children).some(function(child) {
                return (child.innerText || child.textContent || '').trim().length > 0;
            });
            if (childHasOwnText && !isInput) continue;
        }

        const rect = el.getBoundingClientRect();
        if (rect.width <= 0 || rect.height <= 0) continue;
        const style = window.getComputedStyle(el);
        if (style.display === 'none' || style.visibility === 'hidden') continue;

        // Off-canvas elements (a closed side-drawer positioned via
        // translateX(-100%), a carousel item scrolled out of view, etc.)
        // pass every check above - they're not display:none, they have
        // real width/height - but they are NOT actually on screen, so
        // tapping their reported coordinates hits nothing. This checks
        // the element's CENTER point specifically, not just whether any
        // part of its box overlaps the viewport - an element that is
        // mostly off-screen but has one edge poking in still has a
        // center outside the viewport, and a tap at that center (what
        // tap() actually uses) would land in the wrong place or on
        // nothing. Confirmed via a real run: an element whose box
        // technically overlapped the left edge still reported a center
        // x of -34 (off a 1080px-wide screen) and every tap on it was a
        // silent no-op under the weaker box-overlap check.
        const centerX = rect.left + rect.width / 2;
        const centerY = rect.top + rect.height / 2;
        if (centerX < 0 || centerX > window.innerWidth || centerY < 0 || centerY > window.innerHeight) continue;

        const isIconOnly = !text && !isInput;

        if (isIconOnly) {
            // Don't double-count: if a parent element is ALSO clickable
            // and occupies essentially the same box (e.g. a <button>
            // wrapping an <svg>), keep only the outer one.
            let parent = el.parentElement;
            let isDuplicateOfParent = false;
            while (parent) {
                if (isClickable(parent)) {
                    const prect = parent.getBoundingClientRect();
                    if (Math.abs(prect.width - rect.width) < 4 && Math.abs(prect.height - rect.height) < 4) {
                        isDuplicateOfParent = true;
                    }
                    break;
                }
                parent = parent.parentElement;
            }
            if (isDuplicateOfParent) continue;
        }

        results.push({
            text: text || iconLabel(el),
            is_icon_only: isIconOnly,
            is_input: isInput,
            input_type: isInput ? (el.type || 'text') : null,
            placeholder: isInput ? (el.placeholder || '') : '',
            x: rect.left + rect.width / 2,
            y: rect.top + rect.height / 2,
        });
    }

    return JSON.stringify({
        elements: results,
        url: window.location.href,
        viewport_width: window.innerWidth,
        viewport_height: window.innerHeight,
    });
})();"""

GET_FOCUSED_VALUE_JS = """
(function() {
    const el = document.activeElement;
    if (!el) return JSON.stringify({ value: null });
    return JSON.stringify({ value: el.value !== undefined ? el.value : null, tag: el.tagName });
})();"""


def build_set_value_js(text):
    # Sets the value directly via JS/CDP instead of relying on Android's
    # OS-level keyboard simulation, which was found to fail consistently
    # on amount fields even with retries. Uses the native property setter
    # + dispatches a real 'input' event - the correct way to update
    # React's internal state (a plain .value assignment alone does not
    # reliably trigger React's own change detection).
    escaped = json.dumps(text)
    return """
    (function() {
        const el = document.activeElement;
        if (!el) return JSON.stringify({ ok: false, reason: 'no focused element' });
        try {
            const proto = el.tagName === 'TEXTAREA' ? window.HTMLTextAreaElement.prototype : window.HTMLInputElement.prototype;
            const nativeSetter = Object.getOwnPropertyDescriptor(proto, 'value').set;
            nativeSetter.call(el, %s);
            el.dispatchEvent(new Event('input', { bubbles: true }));
            el.dispatchEvent(new Event('change', { bubbles: true }));
            return JSON.stringify({ ok: true, value: el.value });
        } catch (e) {
            return JSON.stringify({ ok: false, reason: String(e) });
        }
    })();
    """ % escaped


FIND_CLOSE_BUTTON_JS = """
(function() {
    const selector = '[aria-label*="close" i], [class*="close" i], [class*="dismiss" i], '
                    + '[id*="close" i], [id*="dismiss" i]';
    const candidates = Array.from(document.querySelectorAll(selector));
    const xCharPattern = /^[x\\u00d7\\u2715\\u2716\\u2717\\u2718]$/i;
    const allElements = Array.from(document.querySelectorAll('*'));
    for (const el of allElements) {
        const text = (el.innerText || el.textContent || '').trim();
        if (xCharPattern.test(text)) candidates.push(el);
    }
    for (const el of candidates) {
        const rect = el.getBoundingClientRect();
        if (rect.width <= 0 || rect.height <= 0) continue;
        const style = window.getComputedStyle(el);
        if (style.display === 'none' || style.visibility === 'hidden') continue;
        return JSON.stringify({ found: true, x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 });
    }
    return JSON.stringify({ found: false });
})();"""


def log(msg):
    print(f"[nav-generic] {msg}")


def run(cmd, timeout=30):
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return result.returncode, result.stdout.strip(), result.stderr.strip()
    except Exception as e:
        return -1, "", str(e)


# =============================================================================
# PHASE 0 - CDP connection (same proven approach as earlier scripts)
# =============================================================================
def is_app_running(package_name):
    rc, out, _ = run(["adb", "shell", "pidof", package_name])
    return bool(out.strip())


def get_foreground_package():
    """Reads which package currently owns the focused window. Needed
    because is_app_running() only checks whether the process EXISTS -
    which stays true even when a tap has opened a system browser/Custom
    Tab on top of the app (the app process is usually still alive in the
    background). That made is_app_running() useless for detecting "we
    got pulled out of the app" - this checks what's actually in front."""
    rc, out, _ = run(["adb", "shell", "dumpsys", "window", "windows"])
    match = re.search(r"mCurrentFocus=.*?\{.*?\s([a-zA-Z0-9_.]+)/", out)
    if match:
        return match.group(1)
    rc, out, _ = run(["adb", "shell", "dumpsys", "activity", "activities"])
    match = re.search(r"mResumedActivity.*?\{.*?\s([a-zA-Z0-9_.]+)/", out)
    if match:
        return match.group(1)
    return None


def is_app_foreground(package_name):
    fg = get_foreground_package()
    if fg is None:
        # Couldn't determine it either way - don't false-trigger the
        # "we left the app" recovery path over a flaky dumpsys parse.
        return True
    return fg == package_name


def find_webview_pid(package_name):
    rc, out, _ = run(["adb", "shell", "pidof", package_name])
    if not out.strip():
        raise RuntimeError(f"Package '{package_name}' does not appear to be running.")
    return out.strip().split()[0]


def reconnect_cdp_with_retry(package_name, attempts=5, delay=1.5):
    """Same as connect_cdp(), but tolerant of the brief window right
    after a Back press where the WebView hasn't registered a CDP page
    target yet. Confirmed via a real run: a single immediate retry
    failed with "No page-type CDP target found" and took down the whole
    exploration - a few retries with a short wait between them is enough
    for the WebView to reattach."""
    last_error = None
    for attempt in range(1, attempts + 1):
        try:
            return connect_cdp(package_name)
        except Exception as e:
            last_error = e
            log(f"Reconnect attempt {attempt}/{attempts} failed ({e}) - retrying...")
            time.sleep(delay)
    raise last_error


def connect_cdp(package_name):
    pid = find_webview_pid(package_name)
    log(f"Found process PID={pid}")
    run(["adb", "forward", f"tcp:{LOCAL_CDP_PORT}", f"localabstract:webview_devtools_remote_{pid}"])
    time.sleep(1)

    import urllib.request
    with urllib.request.urlopen(f"http://localhost:{LOCAL_CDP_PORT}/json", timeout=5) as resp:
        targets = json.loads(resp.read().decode())
    for target in targets:
        if target.get("type") == "page":
            ws = websocket.create_connection(target["webSocketDebuggerUrl"], timeout=10)
            log(f"Connected to CDP target: {target['webSocketDebuggerUrl'][:60]}...")
            return ws
    raise RuntimeError("No page-type CDP target found.")


def cdp_evaluate(ws, expression):
    ws.send(json.dumps({"id": 1, "method": "Runtime.evaluate", "params": {"expression": expression, "returnByValue": True}}))
    while True:
        msg = json.loads(ws.recv())
        if msg.get("id") == 1:
            return msg.get("result", {}).get("result", {}).get("value")


def get_real_screen_size():
    rc, out, _ = run(["adb", "shell", "wm", "size"])
    match = re.search(r"(\d+)x(\d+)", out)
    if not match:
        raise RuntimeError(f"Could not parse screen size from: {out!r}")
    return int(match.group(1)), int(match.group(2))


def compute_scale(viewport_width, viewport_height, real_width, real_height):
    if not viewport_width or not viewport_height:
        return 1.0, 1.0
    return real_width / viewport_width, real_height / viewport_height


def get_elements(ws, scale_x=1.0, scale_y=1.0):
    raw = cdp_evaluate(ws, FIND_ELEMENTS_JS)
    if not raw:
        return [], None
    data = json.loads(raw)
    elements = data.get("elements", [])
    for e in elements:
        e["x"] = e["x"] * scale_x
        e["y"] = e["y"] * scale_y
    return elements, data.get("url")


def find_close_button(ws, scale_x=1.0, scale_y=1.0):
    raw = cdp_evaluate(ws, FIND_CLOSE_BUTTON_JS)
    if not raw:
        return None
    data = json.loads(raw)
    if not data.get("found"):
        return None
    return (data["x"] * scale_x, data["y"] * scale_y)


def wait_for_screen_change(ws, scale_x, scale_y, previous_hash, timeout=SCREEN_SETTLE_TIMEOUT, poll_interval=SCREEN_SETTLE_POLL):
    """Polls until the screen's content hash differs from previous_hash,
    or timeout - handles slow-rendering WebView transitions instead of
    guessing a fixed delay."""
    start = time.time()
    elements, url = [], None
    while time.time() - start < timeout:
        elements, url = get_elements(ws, scale_x, scale_y)
        current_hash = page_state_hash(elements, url or "")
        if current_hash != previous_hash:
            return elements, url, current_hash
        time.sleep(poll_interval)
    current_hash = page_state_hash(elements, url or "")
    return elements, url, current_hash


def page_state_hash(elements, url):
    # Exclude volatile content (live odds, times, dates) from the
    # identity signature so it re-rendering doesn't make a REAL screen
    # look like a new one and drive runaway exploration depth.
    texts = sorted(
        e["text"] for e in elements
        if e.get("text") and not VOLATILE_PAT.match(e["text"].strip())
    )
    signature = url + "|" + "|".join(texts)
    return hashlib.sha1(signature.encode("utf-8")).hexdigest()


# =============================================================================
# Device interaction
# =============================================================================
def tap(x, y):
    run(["adb", "shell", "input", "tap", str(int(x)), str(int(y))])


def get_focused_field_value(ws):
    raw = cdp_evaluate(ws, GET_FOCUSED_VALUE_JS)
    if not raw:
        return None
    return json.loads(raw).get("value")


def set_value_via_cdp(ws, text):
    raw = cdp_evaluate(ws, build_set_value_js(text))
    if not raw:
        return False, None
    data = json.loads(raw)
    return data.get("ok", False), data.get("value")


def type_text(text):
    escaped = text.replace(" ", "%s")
    run(["adb", "shell", "input", "text", escaped])


def find_first_match(elements, keywords, require_input=False):
    for el in elements:
        if require_input and not el.get("is_input"):
            continue
        haystack = (el.get("text", "") + " " + el.get("placeholder", "")).lower()
        if any(kw in haystack for kw in keywords):
            return el
    return None


# =============================================================================
# PHASE 4 - safe back-navigation. HARD GUARANTEE: this function and
# press_back() below are the ONLY places this script ever sends a key
# event to Android, and the only key event ever sent is BACK (4). HOME
# (3) and APP_SWITCH/RECENTS (187) are never sent anywhere in this file.
# =============================================================================
def press_back():
    run(["adb", "shell", "input", "keyevent", "4"])


def navigate_to_hash(ws, scale_x, scale_y, target_hash, home_hash, package_name,
                      max_attempts=4, settle_timeout=4, home_url=None):
    """Returns the app to the screen identified by target_hash by
    pressing Back only as many times as actually needed, checking the
    CURRENT actual screen before every press rather than assuming a
    fixed number of presses. This is what stops the script from ever
    pressing Back once too often from Home and exiting the app: if the
    app's own flow already auto-navigated back to Home (confirmed real
    behavior after some form submissions), the URL is checked - not just
    the full content hash, since a results overlay can still be fading
    out while the URL has already changed - and no further Back press is
    sent from there.

    Before ever sending the hardware Back key, this checks the current
    screen for the app's OWN "<" back control (find_in_app_back_button)
    and taps that instead when present. These apps are hash-routed SPAs
    - the hardware key can have no real back-stack entry to pop and may
    just close the Activity, which is the exact accidental-exit failure
    mode this project has run into before. The app's own back control is
    the app's intended navigation, so it can't do that; the hardware key
    is only used as a fallback on screens that don't have one."""
    target_is_home = target_hash == home_hash

    for attempt in range(max_attempts):
        elements, url = get_elements(ws, scale_x, scale_y)
        current_hash = page_state_hash(elements, url or "")

        if current_hash == target_hash:
            return True, current_hash

        at_home_url = bool(home_url) and url == home_url

        if at_home_url and target_is_home:
            return True, current_hash

        if at_home_url and not target_is_home:
            log(f"Already back at Home ({url}) - stopping Back presses here rather "
                f"than risking exiting the app.")
            return False, current_hash

        if not is_app_running(package_name):
            raise RuntimeError("App closed while trying to navigate back to a known screen.")

        in_app_back = find_in_app_back_button(elements)
        if in_app_back:
            log(f"Not yet at the expected screen (attempt {attempt + 1}/{max_attempts}) - "
                f"tapping the app's own '{in_app_back['text']}' back control at "
                f"({in_app_back['x']:.0f}, {in_app_back['y']:.0f}).")
            tap(in_app_back["x"], in_app_back["y"])
        else:
            log(f"Not yet at the expected screen (attempt {attempt + 1}/{max_attempts}) - "
                f"no in-app back control found here, falling back to the hardware Back key.")
            press_back()
        time.sleep(1.0)

        if not is_app_running(package_name):
            raise RuntimeError("App closed immediately after a Back press while navigating back.")

        elements, url = get_elements(ws, scale_x, scale_y)
        current_hash = page_state_hash(elements, url or "")
        if current_hash != target_hash:
            wait_for_screen_change(ws, scale_x, scale_y, current_hash, timeout=settle_timeout)

    elements, url = get_elements(ws, scale_x, scale_y)
    final_hash = page_state_hash(elements, url or "")
    if final_hash != target_hash:
        log(f"WARNING: could not confirm return to the expected screen after "
            f"{max_attempts} Back press(es). Continuing from whatever screen we're "
            f"actually on now, rather than pressing Back further.")
    return final_hash == target_hash, final_hash


def log_tap(label):
    OUTPUT_DIR.mkdir(exist_ok=True)
    timestamp_ms = int(time.time() * 1000)
    safe_text = label.replace(",", " ").strip() or "(unlabeled element)"
    with open(TAP_LOG_PATH, "a") as f:
        f.write(f"{timestamp_ms},{safe_text}\n")


# =============================================================================
# PHASE 3 - screen-type check: is this screen a fillable form?
# =============================================================================
def find_form_field_and_submit(elements):
    """A screen only counts as a fillable form (amount entry + submit)
    when BOTH a genuine input field AND a submit-style button are
    present together on the SAME screen. Confirmed via a real run
    (bdgwin04.com's Home screen) that treating any lone input field as a
    form - with no submit button anywhere on the page - wrongly ended
    the entire exploration after one screen. Requiring both together
    avoids that false positive without needing any keyword priority
    logic."""
    amount_field = find_first_match(elements, AMOUNT_FIELD_HINTS, require_input=True)
    if not amount_field:
        amount_field = next((e for e in elements if e.get("is_input")), None)
    if not amount_field:
        return None, None
    submit_btn = find_first_match(elements, SUBMIT_KEYWORDS)
    if not submit_btn:
        return None, None
    return amount_field, submit_btn


def fill_and_submit_form(ws, scale_x, scale_y, depth, elements, url, amount_field, submit_btn):
    """PHASE 3b - the actual form-completion flow (what was previously
    called 'the deposit flow'): tap the field, set a test amount via
    CDP, tap submit, wait for and log the results screen. Applies to any
    screen that qualified under find_form_field_and_submit(), not just
    screens with the word 'deposit' on them - the screen shape (input +
    submit together) is what matters, not the label."""
    log(f"[depth {depth}] Form field + submit button both present - "
        f"filling in a test amount and submitting once.")
    log(f"[depth {depth}] Tapping field at ({amount_field['x']:.0f}, {amount_field['y']:.0f})")
    tap(amount_field["x"], amount_field["y"])
    log_tap(f"Form field on {url}")
    time.sleep(0.5)

    log(f"[depth {depth}] Setting amount via CDP: {TARGET_AMOUNT}")
    ok, actual_value = set_value_via_cdp(ws, TARGET_AMOUNT)

    if ok and actual_value and TARGET_AMOUNT in str(actual_value):
        log(f"[depth {depth}] Confirmed: field now contains {actual_value!r} (via CDP)")
    else:
        log(f"[depth {depth}] CDP value-set did not confirm (got {actual_value!r}) - "
            f"falling back to adb-based typing.")
        for attempt in range(1, 3):
            time.sleep(0.5 if attempt == 1 else 1.5)
            type_text(TARGET_AMOUNT)
            time.sleep(0.5)
            actual_value = get_focused_field_value(ws)
            if actual_value and TARGET_AMOUNT in str(actual_value):
                log(f"[depth {depth}] Confirmed: field now contains {actual_value!r} (via adb)")
                break
            tap(amount_field["x"], amount_field["y"])

    fresh_elements, _ = get_elements(ws, scale_x, scale_y)
    fresh_submit = find_first_match(fresh_elements, SUBMIT_KEYWORDS)
    pre_submit_hash = page_state_hash(fresh_elements, url or "")

    if fresh_submit:
        log(f"[depth {depth}] Tapping '{fresh_submit['text']}' at "
            f"({fresh_submit['x']:.0f}, {fresh_submit['y']:.0f})")
        tap(fresh_submit["x"], fresh_submit["y"])
        log_tap(fresh_submit["text"])

        results_elements, results_url, results_hash = wait_for_screen_change(
            ws, scale_x, scale_y, pre_submit_hash
        )
        if results_hash != pre_submit_hash:
            log(f"[depth {depth}] Results screen appeared ({results_url}) - "
                f"{len(results_elements)} element(s): "
                f"{[e['text'] for e in results_elements if e.get('text')]}")
        else:
            log(f"[depth {depth}] WARNING: no new results screen appeared after submitting.")
    else:
        log(f"[depth {depth}] Submit button disappeared before it could be tapped - "
            f"screen likely changed on its own after filling the field.")


# =============================================================================
# PHASE 5 - full DFS exploration: click every clickable, fully explore
# wherever it leads, then come back and move to the next one.
# =============================================================================
def run_exploration(package_name, max_depth):
    ws = connect_cdp(package_name)

    real_width, real_height = get_real_screen_size()
    log(f"Real device screen size: {real_width}x{real_height}")

    raw = cdp_evaluate(ws, FIND_ELEMENTS_JS)
    viewport_w, viewport_h = None, None
    if raw:
        data = json.loads(raw)
        viewport_w, viewport_h = data.get("viewport_width"), data.get("viewport_height")
    scale_x, scale_y = compute_scale(viewport_w, viewport_h, real_width, real_height)
    log(f"CSS viewport: {viewport_w}x{viewport_h} -> scale factor: {scale_x:.2f}x, {scale_y:.2f}y")

    # PHASE 0 - dismiss a blocking popup once up front, if present.
    close_coords = find_close_button(ws, scale_x, scale_y)
    if close_coords:
        x, y = close_coords
        log(f"Dismissing popup at ({x:.0f}, {y:.0f})")
        tap(x, y)
        time.sleep(1.0)

    visited_screen_hashes = set()
    tapped_per_screen = {}
    stats = {"screens_visited": 0, "elements_tapped": 0, "sections_completed": 0}

    # The one screen we must NEVER press Back from - there's nothing
    # left on the back-stack beyond it. Captured once, right after popup
    # dismissal, and checked against (by hash AND by URL) before every
    # single Back press for the rest of the run.
    home_elements, home_url = get_elements(ws, scale_x, scale_y)
    home_hash = page_state_hash(home_elements, home_url or "")
    log(f"Captured Home screen signature ({home_url}) - Back will never be pressed from here.")

    def explore(depth):
        nonlocal ws
        if depth > max_depth:
            log(f"[depth {depth}] Max depth reached - treating this branch as complete.")
            return

        elements, url = get_elements(ws, scale_x, scale_y)
        h = page_state_hash(elements, url or "")

        if h not in visited_screen_hashes:
            visited_screen_hashes.add(h)
            tapped_per_screen[h] = set()
            stats["screens_visited"] += 1
            log(f"[depth {depth}] New screen ({url}) - {len(elements)} element(s) found")

        # PHASE 3 - is this screen a form to fill, rather than a menu to
        # click through? Only true when input + submit are BOTH present.
        amount_field, submit_btn = find_form_field_and_submit(elements)
        if amount_field and submit_btn:
            fill_and_submit_form(ws, scale_x, scale_y, depth, elements, url, amount_field, submit_btn)
            stats["sections_completed"] += 1
            reached, _ = navigate_to_hash(ws, scale_x, scale_y, h, home_hash, package_name, home_url=home_url)
            if not reached:
                log(f"[depth {depth}] Ended up at a different screen than expected after "
                    f"this form (likely the app auto-navigated further on its own) - "
                    f"continuing exploration from there instead of forcing a mismatched Back press.")
            return

        # PHASE 1+2 - generic menu screen: click every clickable element
        # one at a time, in plain top-to-bottom reading order, skipping
        # only what the safety blocklist excludes and what's already
        # been tapped on this exact screen.
        while True:
            elements, url = get_elements(ws, scale_x, scale_y)
            h = page_state_hash(elements, url or "")
            tapped_per_screen.setdefault(h, set())

            candidates = [
                e for e in elements
                if e.get("text")
                # Bare input fields are handled only by the dedicated
                # form branch above. Tapping one here, with nothing lined
                # up to type into it, just pops the on-screen keyboard
                # for no reason - confirmed in a real run ("(icon: input)"
                # tapped with no effect other than that).
                and not e.get("is_input")
                and candidate_key(e) not in tapped_per_screen[h]
                and not is_excluded(e["text"])
            ]
            # Plain reading order - top to bottom, then left to right.
            # No priority/keyword reordering: this is what makes the
            # script generic across apps instead of tuned to one.
            candidates.sort(key=lambda e: (round(e["y"] / 15), e["x"]))
            candidates = candidates[:PER_SCREEN_ELEMENT_LIMIT]

            if not candidates:
                log(f"[depth {depth}] Section fully explored - no remaining clickables.")
                stats["sections_completed"] += 1
                return

            target = candidates[0]
            text, x, y = target["text"], target["x"], target["y"]
            key = candidate_key(target)

            if is_redirect_method_label(text):
                log(f"[depth {depth}] '{text}' is a redirect-type method (e.g. WhatsApp/"
                    f"Telegram) with no real form behind it - noting it without tapping.")
                log_tap(f"Redirect-type method noted (not entered): {text}")
                tapped_per_screen[h].add(key)
                continue

            icon_note = " (icon-only element)" if target.get("is_icon_only") else ""
            log(f"[depth {depth}] Tapping '{text}'{icon_note} at ({x:.0f}, {y:.0f})")

            try:
                tap(x, y)
                log_tap(text)
                tapped_per_screen[h].add(key)
                stats["elements_tapped"] += 1

                new_elements, new_url, new_hash = wait_for_screen_change(ws, scale_x, scale_y, h)

                # Some labels (payment redirects, "Open in browser"-style
                # links not caught by BLOCK_PAT, an SDK's own deep link)
                # can send Android to a DIFFERENT app or a system browser
                # entirely rather than navigating inside this WebView. If
                # our package is no longer the foreground process, there
                # is nothing left in THIS app to explore down that path -
                # recover with one Back press and move on, rather than
                # waiting out the full settle timeout or crashing the
                # whole run on the CDP call that follows.
                if not is_app_foreground(package_name):
                    log(f"[depth {depth}] '{text}' pulled focus away from the app (likely "
                        f"opened an external app/browser on top) - pressing Back once to "
                        f"return and skipping this element rather than following it out.")
                    press_back()
                    time.sleep(1.0)
                    continue

                if new_hash != h:
                    # A new screen (or a revealed menu/overlay) appeared -
                    # fully explore it before coming back here. The nested
                    # explore() call is responsible for getting back to ITS
                    # OWN entry screen (h) before it returns - we never
                    # assume a fixed number of Back presses.
                    explore(depth + 1)

                    reached, _ = navigate_to_hash(ws, scale_x, scale_y, h, home_hash, package_name, home_url=home_url)
                    if reached:
                        log(f"[depth {depth}] Back at the expected screen after exploring '{text}'.")
                    else:
                        log(f"[depth {depth}] Could not confirm return to the exact screen after "
                            f"exploring '{text}' - continuing from wherever we actually are instead "
                            f"of pressing Back further. Remaining candidates on this screen are "
                            f"skipped this pass since we're no longer on it.")
                        return
                else:
                    log(f"[depth {depth}] No screen change after tapping '{text}' (likely an "
                        f"in-place action, e.g. opening a tab on the same page, or a menu panel "
                        f"that doesn't change the URL/content hash - will still try to explore it "
                        f"as a submenu on the next pass of this loop).")

            except websocket.WebSocketConnectionClosedException:
                # The WebView's CDP connection dropped - most likely the
                # tap opened a separate system browser/Custom Tab on top
                # of the app (confirmed as a real pattern in this
                # project: payment-gateway and QR links doing exactly
                # this). Reconnect to the app's WebView rather than
                # letting this kill the whole exploration.
                log(f"[depth {depth}] Lost the WebView connection after tapping '{text}' "
                    f"(likely opened a separate browser/tab outside the app) - pressing "
                    f"Back and reconnecting to continue exploring.")
                press_back()
                time.sleep(1.5)
                try:
                    ws.close()
                except Exception:
                    pass
                ws = reconnect_cdp_with_retry(package_name)
                continue

    try:
        explore(0)
    except websocket.WebSocketConnectionClosedException:
        log("ERROR: Connection to the app was lost mid-session (the app may have crashed "
            "or closed). Stopping here with whatever was captured so far.")
    except Exception as e:
        log(f"ERROR: Unexpected error during exploration: {type(e).__name__}: {e}. "
            f"Stopping here with whatever was captured so far.")

    log(f"Exploration complete. Screens visited: {stats['screens_visited']}, "
        f"elements tapped: {stats['elements_tapped']}, "
        f"sections fully completed: {stats['sections_completed']}")
    try:
        ws.close()
    except Exception:
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package_name")
    parser.add_argument("--max-depth", type=int, default=MAX_DEPTH_DEFAULT)
    args = parser.parse_args()
    run_exploration(args.package_name, args.max_depth)