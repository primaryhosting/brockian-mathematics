#!/usr/bin/env python3
"""conveyor_notify.py — the Conveyor's publish + notify legs.

Three legs, all approval-gated or opt-in — nothing here publishes, deploys,
or emails without an explicit human gate:

1. LOVABLE DRAFT (proved-count change): when a conveyor cycle's registry hop
   changes the PROVED count in registry/theorems.json, build ONE "update the
   proved-theorem showcase" prompt containing the EXACT new theorem names and
   the honest counts read from the registry itself (never fabricated, never
   overclaimed — the prompt states the lake_build-pending posture explicitly:
   AXLE attestation is not a local `lake build`). The prompt goes ONLY to the
   Lovable manager's /queue-submit for project "spectral"; the manager's
   approval gate + pending-approvals queue holds it. Never any publish call.

2. TODAY APPROVAL CARD: for exactly two event kinds — Lovable-draft-ready and
   attest-failure — POST one row to ACUTIS Supabase approval_gates via the
   :18820 proxy (row shape matches the existing writers: conscious_state /
   delegation_executor inserts + routes/missions.js PATCH readers: gate_type,
   title, description, requested_by, risk_level, status=pending, metadata).
   Idempotent: metadata carries a deterministic receipt_id, a state guard
   (state["approval_cards"]) prevents re-posting, and a best-effort server
   probe on metadata->>receipt_id catches a lost state file. If :18820 is
   down the card is queued in state["pending_approval_cards"] and retried
   every cycle.

3. DAILY DIGEST: at the FIRST cycle after 6am local time, emit exactly ONE
   outbox event of kind "conveyor_daily_digest" summarizing the PRIOR day
   (receipts, candidates, chain failures, registry PROVED delta, Paperclip
   issues, drafts, cards) through solver_watch's staging path
   (dispatch_notification): the append-only outbox is the primary channel and
   email stays behind the existing SOLVER_NOTIFY_EMAIL opt-in (default OFF).
   Day stats are accumulated per-cycle in state["daily_stats"] from observed
   cycle results — never reconstructed or estimated after the fact.
"""
from __future__ import annotations

import datetime
import hashlib
import json
import os
import urllib.parse
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
REGISTRY_PATH = os.path.join(REPO, "registry", "theorems.json")

ACUTIS_GATES_URL = os.environ.get(
    "CONVEYOR_ACUTIS_GATES_URL",
    "http://127.0.0.1:18820/api/supabase/approval_gates",
)

DIGEST_HOUR = 6           # first cycle at/after 06:00 local emits yesterday's digest
DAILY_STATS_KEEP = 8      # days of accumulators retained in state
PENDING_CARDS_KEEP = 50
APPROVAL_CARDS_KEEP = 200


def _now_iso() -> str:
    return datetime.datetime.now(datetime.UTC).isoformat()


def _sibling(name):
    """Import a sibling aristotle module under BOTH import styles: package
    (`from aristotle import conveyor_notify`, used by tests from the repo
    root) and script (`python3 aristotle/conveyor.py`, where sys.path[0] is
    this directory)."""
    import importlib
    try:
        return importlib.import_module(f"aristotle.{name}")
    except ImportError:
        return importlib.import_module(name)


def _log(msg):
    # late import so unit tests never touch conveyor's log file wiring
    _sibling("conveyor").log(msg)


# ------------------------------------------------------------ registry snapshot

def registry_proved_snapshot(path=None):
    """Honest read of registry/theorems.json: the PROVED count (from the
    generated summary — the registry value itself), the set of PROVED theorem
    names, and the lake_build posture tally. Returns None when the registry
    is missing/unreadable (callers must treat that as "unknown", never 0)."""
    try:
        with open(path or REGISTRY_PATH, encoding="utf-8") as fh:
            reg = json.load(fh)
    except (OSError, json.JSONDecodeError):
        return None
    theorems = reg.get("theorems") or []
    names = {t.get("name") for t in theorems
             if t.get("register") == "PROVED" and t.get("name")}
    lake = {}
    for t in theorems:
        v = ((t.get("verification") or {}).get("lake_build")) or "unknown"
        lake[v] = lake.get(v, 0) + 1
    count = (reg.get("summary") or {}).get("PROVED")
    if count is None:
        count = len(names)
    return {"count": count, "names": names, "lake_build": lake,
            "total": len(theorems)}


# ------------------------------------------------------------ leg 1: draft prompt

def draft_receipt_id(before_count, after_count, new_names):
    canonical = json.dumps(
        {"before": before_count, "after": after_count,
         "new": sorted(new_names)},
        sort_keys=True, separators=(",", ":")).encode()
    return "conveyor_draft_" + hashlib.sha256(canonical).hexdigest()[:24]


def build_draft_prompt(before, after, max_names=40):
    """The showcase-update prompt. Every number in it is read straight from
    registry/theorems.json snapshots (before/after the registry hop) — the
    counts in the prompt ARE the registry values. Never overclaims: it names
    the lake_build-pending posture and forbids invented claims downstream."""
    new_names = sorted(after["names"] - before["names"])
    removed = sorted(before["names"] - after["names"])
    shown = new_names[:max_names]
    more = len(new_names) - len(shown)
    pending = after["lake_build"].get("pending", 0)
    lines = [
        "Update the proved-theorem showcase on the Spectral site. "
        "Content update ONLY — do not publish or deploy.",
        f"Registry PROVED count changed: {before['count']} -> {after['count']} "
        f"(source: registry/theorems.json summary — use exactly these numbers).",
    ]
    if shown:
        lines.append("Newly PROVED theorem names (exact, from the registry):")
        lines.extend(f"- {n}" for n in shown)
        if more > 0:
            lines.append(f"...and {more} more newly PROVED entries "
                         "(full list in registry/theorems.json).")
    if removed:
        lines.append(
            f"NOTE: {len(removed)} entr{'y' if len(removed) == 1 else 'ies'} "
            f"left the PROVED register — remove or downgrade them honestly: "
            + ", ".join(removed[:10]))
    lines.append(
        "HONESTY POSTURE (must be stated on the page, never softened): these "
        "results are AXLE-attested; local `lake build` verification is still "
        f"pending for {pending} of {after['total']} registry entries. Do not "
        "describe pending entries as lake-built, and do not add any claim not "
        "present in the registry.")
    return "\n".join(lines)


# ------------------------------------------------------------ leg 2: approval cards

def build_draft_ready_gate(receipt_id, before, after, new_names):
    n = len(new_names)
    return {
        "gate_type": "conveyor_lovable_draft",
        "title": (f"Lovable draft ready: proved-theorem showcase "
                  f"{before['count']} -> {after['count']}"),
        "description": (
            f"The Aristotle Conveyor queued a Spectral showcase update on the "
            f"Lovable manager (:18793 /queue-submit, approval-gated there too). "
            f"{n} newly PROVED name(s): "
            + ", ".join(sorted(new_names)[:15])
            + (" ..." if n > 15 else "")
            + ". Counts come straight from registry/theorems.json; "
              "lake_build is still pending for "
            f"{after['lake_build'].get('pending', 0)} of {after['total']} "
            "entries (AXLE-attested only)."),
        "requested_by": "aristotle_conveyor",
        "risk_level": "low",
        "status": "pending",
        "metadata": {"receipt_id": receipt_id, "source": "aristotle_conveyor",
                     "event": "lovable_draft_ready",
                     "proved_before": before["count"],
                     "proved_after": after["count"],
                     "new_proved": sorted(new_names)[:40]},
    }


def attest_failure_receipt_id(reason, fingerprint):
    """Deterministic per (reason, attest fingerprint) ONLY — never the digest
    receipts. run_cycle step 3 consumes the digests even when the registry hop
    fails the truth gate (its cursor is the attest fingerprint, not the
    receipts), so a receipts-bearing id would change on the retry cycle
    (digests=[]) and double-post the identical failure's Today card. reason
    already encodes stage+rc; fp pins the attestation set."""
    canonical = json.dumps(
        {"reason": reason, "fp": fingerprint},
        sort_keys=True, separators=(",", ":")).encode()
    return "conveyor_attest_fail_" + hashlib.sha256(canonical).hexdigest()[:24]


def build_attest_failure_gate(receipt_id, reason, detail=""):
    return {
        "gate_type": "conveyor_attest_failure",
        "title": f"Conveyor attest failure: {reason[:120]}",
        "description": (
            "The Aristotle Conveyor's verify/attest cycle stopped and will "
            "retry next cycle (cursor NOT advanced; the truth gate is never "
            f"bypassed). Reason: {reason}. "
            + (f"Detail: {detail[:500]} " if detail else "")
            + "Evidence: aristotle/conveyor.log + conveyor_state.json "
              "(last_cycle.stages)."),
        "requested_by": "aristotle_conveyor",
        "risk_level": "medium",
        "status": "pending",
        "metadata": {"receipt_id": receipt_id, "source": "aristotle_conveyor",
                     "event": "attest_failure", "reason": reason},
    }


def post_approval_gate(payload, url=None, opener=None):
    """POST one approval_gates row through the ACUTIS proxy. Returns the
    created row dict (Prefer: return=representation) or None on failure."""
    req = urllib.request.Request(
        url or ACUTIS_GATES_URL,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json",
                 "Prefer": "return=representation"},
        method="POST",
    )
    try:
        with (opener or urllib.request.urlopen)(req, timeout=15) as r:
            body = json.loads(r.read() or b"null")
        row = body[0] if isinstance(body, list) and body else body
        if not isinstance(row, dict) or not row.get("id"):
            _log("approval_gates POST returned unexpected body; treating as failure")
            return None
        return row
    except Exception as e:  # noqa: BLE001
        _log(f"approval_gates POST unavailable ({e}); queuing card in state")
        return None


def gate_exists_serverside(receipt_id, url=None, opener=None):
    """Best-effort probe for a card already carrying this receipt_id (covers
    a lost/rolled-back state file). Only rows whose metadata is a jsonb
    OBJECT match (ours are); any error means 'unknown' -> False."""
    q = urllib.parse.urlencode({
        "metadata->>receipt_id": f"eq.{receipt_id}",
        "select": "id", "limit": "1"})
    req = urllib.request.Request(f"{url or ACUTIS_GATES_URL}?{q}")
    try:
        with (opener or urllib.request.urlopen)(req, timeout=10) as r:
            rows = json.loads(r.read() or b"[]")
        return bool(isinstance(rows, list) and rows)
    except Exception:  # noqa: BLE001
        return False


def _persist(state, state_path):
    if state_path:
        _sibling("conveyor")._atomic_json_dump(state, state_path)


def _trim_cards(cards):
    """approval_cards is the idempotency guard; cap it by insertion order
    (dicts preserve it) so state never grows without bound."""
    if len(cards) <= APPROVAL_CARDS_KEEP:
        return cards
    return dict(list(cards.items())[-APPROVAL_CARDS_KEEP:])


def post_approval_card(state, receipt_id, payload, poster=None, prober=None,
                       state_path=None):
    """Idempotently post one Today approval card. Guard order: state guard
    (primary), then server-side receipt probe (belt-and-braces), then POST.
    Failure queues the card in state["pending_approval_cards"] for retry.
    Returns True when a card was actually created."""
    poster = poster or post_approval_gate
    prober = prober or gate_exists_serverside
    cards = state.setdefault("approval_cards", {})
    if receipt_id in cards:
        return False
    pending = state.setdefault("pending_approval_cards", [])
    if any(p.get("receipt_id") == receipt_id for p in pending):
        return False
    if prober(receipt_id):
        cards[receipt_id] = {"note": "found serverside", "at": _now_iso()}
        state["approval_cards"] = _trim_cards(cards)
        _persist(state, state_path)
        return False
    row = poster(payload)
    if row:
        cards[receipt_id] = {"gate_id": row.get("id"), "created_at": _now_iso()}
        state["approval_cards"] = _trim_cards(cards)
        _persist(state, state_path)
        return True
    pending.append({"receipt_id": receipt_id, "payload": payload,
                    "queued_at": _now_iso()})
    state["pending_approval_cards"] = pending[-PENDING_CARDS_KEEP:]
    return False


def flush_pending_approval_cards(state, poster=None, prober=None,
                                 state_path=None):
    """Retry cards queued while :18820 was down. Returns number delivered."""
    poster = poster or post_approval_gate
    prober = prober or gate_exists_serverside
    pending = state.get("pending_approval_cards") or []
    if not pending:
        return 0
    state["pending_approval_cards"] = []
    delivered = 0
    for item in pending:
        if post_approval_card(state, item.get("receipt_id"),
                              item.get("payload") or {}, poster=poster,
                              prober=prober, state_path=state_path):
            delivered += 1
    return delivered


# ------------------------------------------------------------ leg 3: daily digest

def local_now():
    return datetime.datetime.now()


def digest_day(now=None):
    """The day a digest emitted 'now' covers: yesterday, local time."""
    d = (now or local_now()).date() - datetime.timedelta(days=1)
    return d.isoformat()


def should_emit_daily_digest(now, last_emitted_for):
    """True at the FIRST cycle at/after 06:00 local whose prior-day digest has
    not been emitted yet. Before 06:00 nothing fires (yesterday may still be
    accumulating a pre-6am cycle's stats is fine — the boundary is the hour).
    last_emitted_for is the day (YYYY-MM-DD) the last digest covered."""
    if now.hour < DIGEST_HOUR:
        return False
    return last_emitted_for != digest_day(now)


def accumulate_daily_stats(state, cycle, proved_count, now=None):
    """Fold one observed cycle into today's accumulator. Every field is a
    count of things that actually happened this cycle — nothing inferred."""
    day = (now or local_now()).date().isoformat()
    stats_all = state.setdefault("daily_stats", {})
    s = stats_all.setdefault(day, {
        "cycles": 0, "receipts": 0, "candidates": 0, "chain_failures": 0,
        "failure_reasons": [], "registry_hops_ok": 0, "registry_hops_stopped": 0,
        "paperclip_issues": 0, "lovable_drafts": 0, "approval_cards": 0,
        "proved_first": proved_count, "proved_last": proved_count,
    })
    s["cycles"] += 1
    s["receipts"] += cycle.get("new_receipts", 0)
    s["candidates"] += len(cycle.get("candidates") or [])
    if cycle.get("stopped_reason"):
        s["chain_failures"] += 1
        s["failure_reasons"] = (s["failure_reasons"]
                                + [cycle["stopped_reason"]])[-10:]
    hop = cycle.get("registry_hop") or {}
    if hop.get("ran"):
        if hop.get("ok"):
            s["registry_hops_ok"] += 1
        else:
            s["registry_hops_stopped"] += 1
    s["paperclip_issues"] += cycle.get("paperclip_issues_filed", 0)
    s["lovable_drafts"] += cycle.get("lovable_drafts_queued", 0)
    # cards delivered from the retry queue (queued during a :18820 outage,
    # flushed this cycle) are posted cards too — count both
    s["approval_cards"] += (cycle.get("approval_cards_posted", 0)
                            + cycle.get("approval_cards_flushed", 0))
    if s.get("proved_first") is None:
        s["proved_first"] = proved_count
    if proved_count is not None:
        s["proved_last"] = proved_count
    # prune old days
    for old in sorted(stats_all)[:-DAILY_STATS_KEEP]:
        del stats_all[old]
    return s


def build_daily_digest(stats, day):
    """(subject, body) for one day's accumulator. stats=None -> an honest
    'no cycles observed' digest, never invented numbers."""
    if not stats:
        subject = f"Aristotle Conveyor daily digest — {day}"
        body = (f"No conveyor cycles were observed on {day} "
                "(agent down or machine asleep). No work is claimed.")
        return subject, body
    pf, pl = stats.get("proved_first"), stats.get("proved_last")
    if pf is None or pl is None:
        delta_line = "registry PROVED delta: unknown (registry unreadable)"
    else:
        delta_line = f"registry PROVED: {pf} -> {pl} (delta {pl - pf:+d})"
    lines = [
        f"Aristotle Conveyor — {day} summary "
        f"({stats['cycles']} cycle(s) observed):",
        f"- solver digests processed: {stats['receipts']} "
        f"({stats['candidates']} candidate(s) parsed)",
        f"- chain failures: {stats['chain_failures']}"
        + (f" — {'; '.join(stats['failure_reasons'][-3:])}"
           if stats["failure_reasons"] else ""),
        f"- registry hops: {stats['registry_hops_ok']} ok, "
        f"{stats['registry_hops_stopped']} stopped by the truth gate",
        f"- {delta_line}",
        f"- Paperclip attribution issues created: {stats['paperclip_issues']}",
        f"- Lovable showcase drafts queued (approval-gated): "
        f"{stats['lovable_drafts']}",
        f"- Today approval cards posted: {stats['approval_cards']}",
        "",
        "All numbers are observed counts from conveyor_state.json; "
        "the outbox + Today tile is the primary channel "
        "(email only under SOLVER_NOTIFY_EMAIL=1).",
    ]
    return f"Aristotle Conveyor daily digest — {day}", "\n".join(lines)


def _missed_digest_days(last_emitted_for, digest_day_str, stats_all):
    """Un-digested days strictly between last_emitted_for and digest_day that
    have OBSERVED stats (retained DAILY_STATS_KEEP days). Days with no stats
    are skipped silently — only digest_day itself gets the honest 'no cycles
    observed' digest. Bounded by the stats retention window; a malformed
    guard value yields no catch-up rather than a crash."""
    if not last_emitted_for:
        return []
    try:
        d = datetime.date.fromisoformat(last_emitted_for)
        end = datetime.date.fromisoformat(digest_day_str)
    except ValueError:
        return []
    days = []
    d += datetime.timedelta(days=1)
    while d < end:
        if d.isoformat() in stats_all:
            days.append(d.isoformat())
        d += datetime.timedelta(days=1)
    return days


def emit_daily_digest(state, now=None, dispatcher=None, state_path=None):
    """At the first cycle after 6am, stage ONE conveyor_daily_digest outbox
    event for the prior day via solver_watch's staging path (which also
    honors the SOLVER_NOTIFY_EMAIL opt-in, default OFF) — plus one catch-up
    digest per earlier un-digested day that has observed stats (machine down
    across a 6am window must not silently drop a day's real work). The guard
    is state["daily_digest_emitted_for"], advanced + persisted immediately
    after EACH dispatch so a crash cannot double-send. Returns the prior-day
    digest's receipt info or None."""
    now = now or local_now()
    if not should_emit_daily_digest(now, state.get("daily_digest_emitted_for")):
        return None
    day = digest_day(now)
    stats_all = state.get("daily_stats") or {}
    if (state.get("daily_digest_emitted_for") is None
            and day not in stats_all):
        # first run with no observed prior-day stats: baseline the guard
        # without claiming anything (solver_watch first-run convention)
        state["daily_digest_emitted_for"] = day
        _persist(state, state_path)
        _log(f"daily digest baselined at {day} (first run, no observed stats)")
        return None
    if dispatcher is None:
        dispatcher = _sibling("solver_watch").dispatch_notification
    result = None
    days = _missed_digest_days(
        state.get("daily_digest_emitted_for"), day, stats_all) + [day]
    for d in days:
        subject, body = build_daily_digest(stats_all.get(d), d)
        result = dispatcher(subject, body, kind="conveyor_daily_digest")
        state["daily_digest_emitted_for"] = d
        _persist(state, state_path)
        _log(f"daily digest emitted for {d}: {result}")
    return result
