#!/usr/bin/env python3
"""conveyor.py — the Aristotle Conveyor: outbox → verify/attest chain → registry.

A SHORT-LIVED cycle process (run by launchd every 15 min; runs and exits — never
a resident daemon). Each cycle:

  1. Reads solver_notification_outbox.jsonl (append-only, written by
     solver_watch.py) and finds solver_completion_digest events whose receipt_id
     is not yet in conveyor_cursor.json. Parses the CANDIDATE entries
     (account + project name + uuid) out of each digest body.
  2. Only when NEW candidates exist since the cursor does it invoke the heavy
     verify/attest chain — the same stages run-morning-verify.sh runs, with the
     same caps (HARVEST_ALL_MAX, AXLE_MAX, CROSS_MAX, AUTO_PR_LIVE=0 forced).
     A fatal stage failure records state and stops the cycle cleanly; the cursor
     is NOT advanced, so the next cycle retries. verify_stage.py gets a bounded
     wall-clock budget instead (it persists per-file state and is resumable, and
     downstream stages tolerate unknown compile status), so budget exhaustion is
     recorded but non-fatal — exactly how the existing pipeline treats the slow
     local-lake leg vs the fast AXLE leg.
  3. Registry hop, gated on TRUTH: only when the registry/attestations/*
     fingerprint changed since the last recorded one (first run records a
     baseline, mirroring solver_watch's first-run behavior) does it run
     gen_registry → audit_registry_consistency --strict. An audit failure STOPS
     the hop and records why — it is never bypassed. Only after a clean audit do
     gen_claims + gen_observatory run. (Verified property: with no new
     attestations, gen_registry regeneration is byte-identical, so skipping it
     is a no-op by construction.)
  4. Notifies the Lovable manager ONLY via POST /queue-submit on :18793 with
     project key "spectral" — the manager's approval gate + pending-approvals
     queue is the point; the conveyor never publishes or deploys. If :18793 is
     down the event is queued in conveyor_state.json and retried next cycle.

State + cursor use atomic writes (temp + fsync + rename — the same pattern as
solver_watch._atomic_json_dump) so a crash or ENOSPC preserves the prior file.
"""
from __future__ import annotations

import datetime
import fcntl
import glob
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
OUTBOX = os.environ.get(
    "SOLVER_NOTIFICATION_OUTBOX",
    os.path.join(HERE, "solver_notification_outbox.jsonl"),
)
CURSOR = os.path.join(HERE, "conveyor_cursor.json")
STATE = os.path.join(HERE, "conveyor_state.json")
LOG = os.path.join(HERE, "conveyor.log")
LOCK = os.path.join(HERE, ".conveyor.lock")
ATTEST_DIR = os.path.join(REPO, "registry", "attestations")

LOVABLE_QUEUE_SUBMIT = os.environ.get(
    "CONVEYOR_LOVABLE_URL", "http://127.0.0.1:18793/queue-submit"
)
LOVABLE_PROJECT = "spectral"  # dd8308ac — owner-confirmed canonical

DIGEST_KIND = "solver_completion_digest"
HISTORY_KEEP = 20
PENDING_LOVABLE_KEEP = 50

# One CANDIDATE line in a digest body, followed by an indented project uuid:
#   🧪 CANDIDATE [admin] arsub_cb6e_e_s
#     616689d7-3883-46f8-a891-74744d38217c
CANDIDATE_LINE = re.compile(r"CANDIDATE\s+\[(\w+)\]\s+(\S+)")
UUID_LINE = re.compile(r"^\s+([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\s*$")

PY = sys.executable or "/opt/homebrew/bin/python3"


def _now() -> str:
    return datetime.datetime.now(datetime.UTC).isoformat()


def log(msg: str) -> None:
    line = f"{_now()} {msg}"
    print(line)
    try:
        with open(LOG, "a") as fh:
            fh.write(line + "\n")
    except Exception:
        pass


def _atomic_json_dump(obj, path, indent=1):
    """Write JSON to a temp file, fsync, then rename into place (solver_watch
    pattern). On ENOSPC the dump raises against the .tmp file and the prior
    good file is preserved."""
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh, indent=indent)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def load_json(path, default):
    try:
        with open(path) as fh:
            return json.load(fh)
    except FileNotFoundError:
        return default
    except Exception as e:
        # A present-but-unparseable file is a real problem — surface it instead
        # of silently resetting (solver_watch convention).
        log(f"WARNING: {path} exists but failed to parse ({e}); using default")
        return default


# ---------------------------------------------------------------- outbox / cursor

def read_outbox_events(path=None):
    events = []
    try:
        with open(path or OUTBOX, encoding="utf-8") as fh:
            for line in fh:
                if not line.strip():
                    continue
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError:
                    log("ignored malformed notification outbox line")
    except (FileNotFoundError, OSError):
        pass
    return events


def new_digests(events, processed_ids):
    """Digest events (staged, solver_completion_digest) not yet processed,
    in outbox (chronological) order, deduped by receipt_id."""
    seen = set()
    out = []
    for ev in events:
        if ev.get("event") != "notification.staged":
            continue
        if ev.get("kind") != DIGEST_KIND:
            continue
        rid = ev.get("receipt_id")
        if not rid or rid in processed_ids or rid in seen:
            continue
        seen.add(rid)
        out.append(ev)
    return out


def parse_candidates(body):
    """Parse CANDIDATE entries out of a digest body: account + name + uuid.

    The uuid sits on the indented line after its CANDIDATE line; a CANDIDATE
    line with no following uuid line still yields an entry (uuid=None)."""
    out = []
    pending = None
    for line in (body or "").splitlines():
        m = CANDIDATE_LINE.search(line)
        if m:
            pending = {"account": m.group(1), "name": m.group(2), "uuid": None}
            out.append(pending)
            continue
        if pending is not None:
            u = UUID_LINE.match(line)
            if u:
                pending["uuid"] = u.group(1)
            pending = None
    return out


# ---------------------------------------------------------------- verify chain

class StageResult(dict):
    pass


def _run_stage(name, script, env_extra=None, timeout=1800, timeout_fatal=True):
    """Run one chain stage as a subprocess in its own session; on wall-clock
    timeout the whole process group is killed (lake/lean grandchildren too)."""
    env = dict(os.environ)
    env.update(env_extra or {})
    started = datetime.datetime.now(datetime.UTC)
    try:
        proc = subprocess.Popen(
            [PY, os.path.join(HERE, script)],
            cwd=REPO, env=env, start_new_session=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        try:
            out, _ = proc.communicate(timeout=timeout)
            rc = proc.returncode
            status = "ok" if rc == 0 else "failed"
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            out, _ = proc.communicate()
            rc = None
            status = "budget_exhausted" if not timeout_fatal else "timeout"
    except Exception as e:  # noqa: BLE001
        out, rc, status = str(e), None, "error"
    seconds = (datetime.datetime.now(datetime.UTC) - started).total_seconds()
    tail = (out or "").strip()[-500:]
    log(f"stage {name}: {status} rc={rc} {seconds:.0f}s")
    return StageResult(name=name, status=status, rc=rc,
                       seconds=round(seconds, 1), tail=tail)


def chain_stages():
    """The verify/attest chain — the same stages run-morning-verify.sh runs,
    with the same caps. AUTO_PR_LIVE=0 is forced: the public GitHub mutation
    stays behind the existing human gate."""
    axle_max = os.environ.get("AXLE_MAX", "120")
    harvest_all_max = os.environ.get("HARVEST_ALL_MAX", "80")
    cross_max = os.environ.get("CROSS_MAX", "6")
    verify_budget = int(os.environ.get("CONVEYOR_VERIFY_BUDGET", "900"))
    stage_timeout = int(os.environ.get("CONVEYOR_STAGE_TIMEOUT", "1800"))
    return [
        # (name, script, env, timeout, timeout_fatal)
        ("harvest_proofs", "harvest_proofs.py", {}, stage_timeout, True),
        ("harvest_all", "harvest_all.py",
         {"HARVEST_ALL_MAX": harvest_all_max}, stage_timeout, True),
        # verify_stage persists per-file state and is resumable; the local lake
        # leg cannot clear the backlog in one cycle by design, so its budget
        # exhaustion is recorded but NON-fatal (AXLE is the independent leg).
        ("verify_stage", "verify_stage.py", {}, verify_budget, False),
        ("select_best", "select_best.py", {}, stage_timeout, True),
        ("axle_verify", "axle_verify.py", {"AXLE_MAX": axle_max}, stage_timeout, True),
        ("catalogue_domains", "catalogue_domains.py", {}, stage_timeout, True),
        ("lemma_mine", "lemma_mine.py", {}, stage_timeout, True),
        ("reduction_tracker", "reduction_tracker.py", {}, stage_timeout, True),
        ("cross_check", "cross_check.py", {"CROSS_MAX": cross_max}, stage_timeout, True),
        ("minimize_proofs", "minimize_proofs.py", {}, stage_timeout, True),
        ("annotate_headers", "annotate_headers.py", {}, stage_timeout, True),
        ("auto_pr", "auto_pr.py", {"AUTO_PR_LIVE": "0"}, stage_timeout, True),
        ("observatory", "observatory.py", {}, stage_timeout, True),
    ]


def run_chain(runner=_run_stage, stages=None):
    """Run the chain in order. Returns (results, ok). A fatal failure stops the
    chain; budget_exhausted on a non-fatal stage continues."""
    results = []
    for name, script, env, timeout, timeout_fatal in (stages or chain_stages()):
        res = runner(name, script, env_extra=env, timeout=timeout,
                     timeout_fatal=timeout_fatal)
        results.append(res)
        if res["status"] in ("failed", "timeout", "error"):
            return results, False
    return results, True


# ---------------------------------------------------------------- registry hop

def attestation_fingerprint(attest_dir=None):
    """Stable fingerprint over registry/attestations/*.json contents."""
    h = hashlib.sha256()
    for path in sorted(glob.glob(os.path.join(attest_dir or ATTEST_DIR, "*.json"))):
        with open(path, "rb") as fh:
            digest = hashlib.sha256(fh.read()).hexdigest()
        h.update(f"{os.path.basename(path)}:{digest}\n".encode())
    return h.hexdigest()


def _run_repo_script(name, args, timeout=900):
    started = datetime.datetime.now(datetime.UTC)
    try:
        r = subprocess.run([PY, *args], cwd=REPO, capture_output=True,
                           text=True, timeout=timeout)
        rc, out = r.returncode, (r.stdout or "") + (r.stderr or "")
        status = "ok" if rc == 0 else "failed"
    except Exception as e:  # noqa: BLE001
        rc, out, status = None, str(e), "error"
    seconds = (datetime.datetime.now(datetime.UTC) - started).total_seconds()
    log(f"registry hop {name}: {status} rc={rc} {seconds:.0f}s")
    return StageResult(name=name, status=status, rc=rc,
                       seconds=round(seconds, 1), tail=out.strip()[-500:])


def run_registry_hop(runner=_run_repo_script):
    """gen_registry → audit --strict (failure = STOP, never bypass) →
    gen_claims → gen_observatory. Returns (results, ok, stop_reason)."""
    results = []
    res = runner("gen_registry", ["scripts/gen_registry.py"])
    results.append(res)
    if res["status"] != "ok":
        return results, False, "gen_registry failed"
    res = runner("audit_strict", ["scripts/audit_registry_consistency.py", "--strict"])
    results.append(res)
    if res["status"] != "ok":
        # TRUTH GATE: an audit failure stops this hop. It is never bypassed.
        return results, False, "audit_registry_consistency --strict failed"
    res = runner("gen_claims", ["scripts/gen_claims.py"])
    results.append(res)
    if res["status"] != "ok":
        return results, False, "gen_claims failed"
    res = runner("gen_observatory", ["scripts/gen_observatory.py"])
    results.append(res)
    if res["status"] != "ok":
        return results, False, "gen_observatory failed"
    return results, True, None


# ---------------------------------------------------------------- lovable queue

def post_lovable_queue(prompt, url=None, opener=None):
    """Submit ONE prompt to the Lovable manager /queue-submit (project key
    "spectral"). The manager's approval gate decides what happens next; the
    conveyor never touches any publish/deploy path. Returns True on success."""
    payload = json.dumps(
        {"items": [{"project": LOVABLE_PROJECT, "prompt": prompt}]}
    ).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    # Same token fallback chain as lovable_grader.py; the manager fails closed
    # without it. The wrapper script exports it from the manager's own plist.
    token = (os.environ.get("LOVABLE_MANAGER_TOKEN")
             or os.environ.get("LOVABLE_MANAGER_AUTH_TOKEN")
             or os.environ.get("OPENCLAW_AUTH_TOKEN")
             or os.environ.get("AUTH_TOKEN") or "").strip()
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(
        url or LOVABLE_QUEUE_SUBMIT, data=payload,
        headers=headers, method="POST",
    )
    try:
        with (opener or urllib.request.urlopen)(req, timeout=15) as r:
            r.read()
        return True
    except Exception as e:  # noqa: BLE001
        log(f"lovable queue-submit unavailable ({e}); queuing event in state")
        return False


def flush_pending_lovable(state, poster=None):
    """Try to deliver queued events; keep the ones that still fail."""
    poster = poster or post_lovable_queue
    pending = state.get("pending_lovable_events") or []
    still = []
    for ev in pending:
        if poster(ev.get("prompt", "")):
            log(f"delivered queued lovable event from {ev.get('queued_at')}")
        else:
            still.append(ev)
    state["pending_lovable_events"] = still[-PENDING_LOVABLE_KEEP:]
    return len(pending) - len(still)


def queue_or_send_lovable(state, prompt, poster=None):
    poster = poster or post_lovable_queue
    if not poster(prompt):
        state.setdefault("pending_lovable_events", []).append(
            {"queued_at": _now(), "project": LOVABLE_PROJECT, "prompt": prompt}
        )
        state["pending_lovable_events"] = \
            state["pending_lovable_events"][-PENDING_LOVABLE_KEEP:]
        return False
    return True


# ---------------------------------------------------------------- cycle summary

def _axle_counts():
    """Honest counts from the actual AXLE state file (never fabricated)."""
    st = load_json(os.path.join(HERE, "axle_verify.json"), {})
    verified = sum(1 for v in st.values()
                   if isinstance(v, dict) and v.get("verified") is True)
    return {"axle_entries": len(st), "axle_verified": verified}


def notify_key(digests, fp, chain_ok):
    """Dedupe key for the Lovable status card: same receipts + same
    attestation fingerprint + same chain outcome = the same card. Stored in
    state["last_notified"] so an unchanged repeat is never re-queued."""
    rids = ",".join(sorted(ev.get("receipt_id") or "" for ev in digests))
    return hashlib.sha256(f"{rids}|{fp}|{chain_ok}".encode()).hexdigest()


def build_lovable_prompt(cycle):
    cands = cycle.get("candidates") or []
    names = ", ".join(sorted({c["name"] for c in cands})[:20])
    ax = _axle_counts()
    reg = cycle.get("registry_hop") or {}
    reg_line = (
        "registry regenerated and audit --strict passed"
        if reg.get("ok")
        else f"registry hop stopped: {reg.get('stop_reason')}"
        if reg.get("ran")
        else "registry unchanged (no new attestations)"
    )
    return (
        f"Aristotle Conveyor status update ({cycle.get('finished_at') or _now()}). "
        f"Content update ONLY — do not publish or deploy. "
        f"New solver completion digests processed: {cycle.get('new_receipts', 0)}; "
        f"CANDIDATE entries parsed: {len(cands)}"
        + (f" ({names})" if names else "")
        + f". AXLE verification state: {ax['axle_verified']} of "
          f"{ax['axle_entries']} best proofs independently AXLE-verified. "
        + f"Registry: {reg_line}. "
          "Please refresh the Aristotle / Verified Frontier status counters on "
          "the Spectral showcase with exactly these numbers — no other claims."
    )


# ---------------------------------------------------------------- main cycle

def run_cycle():
    cursor = load_json(CURSOR, {})
    state = load_json(STATE, {})
    processed = set(cursor.get("processed_receipt_ids") or [])
    first_run = not os.path.exists(CURSOR)

    cycle = {"started_at": _now(), "new_receipts": 0, "candidates": [],
             "stages": [], "registry_hop": {"ran": False}, "stopped_reason": None}

    # 0. retry lovable events queued while :18793 was down (cheap; every cycle)
    flushed = flush_pending_lovable(state)
    if flushed:
        cycle["lovable_flushed"] = flushed
        # Persist the drained pending list NOW: the heavy chain below can run
        # for hours, and a crash before the end-of-cycle dump would resurrect
        # already-delivered events next cycle (duplicate delivery).
        _atomic_json_dump(state, STATE)

    # 1. read outbox from the cursor
    digests = new_digests(read_outbox_events(), processed)
    candidates = []
    for ev in digests:
        candidates.extend(parse_candidates(ev.get("body", "")))
    cycle["new_receipts"] = len(digests)
    cycle["candidates"] = candidates
    log(f"outbox: {len(digests)} new digest(s), {len(candidates)} candidate(s)")

    chain_ok = True
    if digests:
        # don't stack on an already-grinding verify (morning-verify guard)
        probe = subprocess.run(["pgrep", "-f", "verify_stage.py"],
                               capture_output=True)
        if probe.returncode == 0:
            cycle["stopped_reason"] = "verify_stage already running; deferred"
            log(cycle["stopped_reason"])
            chain_ok = False
        else:
            results, chain_ok = run_chain()
            cycle["stages"] = list(results)
            if not chain_ok:
                bad = results[-1]
                cycle["stopped_reason"] = (
                    f"stage {bad['name']} {bad['status']} (rc={bad['rc']})")
    else:
        log("no new candidates since cursor; heavy chain skipped")

    # 2. registry hop — only on a NEW attestation fingerprint (truth-gated)
    fp = attestation_fingerprint()
    last_fp = cursor.get("attestation_fingerprint")
    if last_fp is None:
        cycle["registry_hop"] = {
            "ran": False, "ok": None,
            "note": "first run: attestation fingerprint baselined "
                    "(pre-existing backlog is not claimed as new attest work)",
        }
        cursor["attestation_fingerprint"] = fp
    elif fp != last_fp and chain_ok:
        results, ok, why = run_registry_hop()
        cycle["registry_hop"] = {"ran": True, "ok": ok, "stop_reason": why,
                                 "stages": list(results)}
        if ok:
            cursor["attestation_fingerprint"] = fp
        else:
            cycle["stopped_reason"] = cycle["stopped_reason"] or why
    elif fp != last_fp:
        cycle["registry_hop"] = {
            "ran": False, "ok": None,
            "note": "attestations changed but chain did not complete; "
                    "hop deferred to next cycle"}
    # fp == last_fp → nothing to do; gen_registry would be byte-identical
    # (verified property), so skipping is a no-op by construction.

    # 3. advance the cursor only after a completed chain (idempotent retries)
    if digests and chain_ok:
        processed.update(ev["receipt_id"] for ev in digests)
        cursor["processed_receipt_ids"] = sorted(processed)
    cursor["updated_at"] = _now()

    cycle["finished_at"] = _now()

    # 4. notify (queue-submit only; approval-gated downstream). Only COMPLETED
    # work notifies: a failed or deferred chain keeps the cursor, so notifying
    # would queue a near-duplicate card every 15 min for the whole outage — and
    # each card would falsely claim "digests processed: N". Belt-and-braces, a
    # dedupe key over (receipts, fingerprint, outcome) skips unchanged repeats
    # (e.g. a registry hop failing the same way on the same attestations).
    did_work = (bool(digests) and chain_ok) or cycle["registry_hop"].get("ran")
    key = notify_key(digests, fp, chain_ok)
    if did_work and not first_run and state.get("last_notified") != key:
        queue_or_send_lovable(state, build_lovable_prompt(cycle))
        state["last_notified"] = key

    state["updated_at"] = _now()
    state["last_cycle"] = cycle
    history = state.get("history") or []
    history.append({k: cycle.get(k) for k in
                    ("started_at", "finished_at", "new_receipts",
                     "stopped_reason")})
    state["history"] = history[-HISTORY_KEEP:]
    _atomic_json_dump(state, STATE)
    _atomic_json_dump(cursor, CURSOR)
    log(f"cycle done: receipts={len(digests)} chain_ok={chain_ok} "
        f"registry_hop={cycle['registry_hop'].get('ran')} "
        f"stopped={cycle['stopped_reason']}")
    return cycle


def main():
    # single-instance lock: a short-lived cycle process, never a daemon
    lock_fh = open(LOCK, "w")
    try:
        fcntl.flock(lock_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log("another conveyor cycle is running; exiting")
        return 0
    try:
        run_cycle()
    finally:
        fcntl.flock(lock_fh, fcntl.LOCK_UN)
        lock_fh.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
