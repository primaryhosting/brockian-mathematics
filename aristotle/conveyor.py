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
  5. SPEND ATTRIBUTION (Paperclip): per candidate batch (= one solver digest
     receipt) it POSTs exactly ONE Riemann Labs issue to Paperclip :3101 —
     "Aristotle: <project> — candidate ready" with the candidates + local
     verdict-evidence links in the body. The Paperclip create endpoint IGNORES
     client-supplied originFingerprint (verified 2026-08-18: the probe's
     originKind/originFingerprint came back "manual"/"default"), so the API
     provides NO dedupe — idempotency is guarded client-side in
     conveyor_state.json ("paperclip_issues", keyed by receipt_id) and the
     state is persisted immediately after each successful POST, so re-running
     a cycle NEVER duplicates an issue. If :3101 is down the payload is queued
     in state["pending_paperclip"] and retried every cycle (the cursor can
     advance past the receipt, so the pending queue — not the outbox — is the
     retry path, mirroring pending_lovable_events). It also files ONE weekly
     RIE issue requesting a Hermes proof attempt against this repo — the
     replacement for the dead ~/.hermes/cron/proof-attempt.json nightly job
     (the hermes cron scheduler only loads cron/jobs.json; the per-name file
     was never executed and now carries enabled:false). Issues are left
     UNASSIGNED (NOETHER is in an error state and must not be assigned).

  6. PUBLISH + NOTIFY legs (conveyor_notify.py): a registry hop that changed
     the PROVED count queues ONE honest showcase-update draft on the Lovable
     manager (queue-submit only, approval-gated); Lovable-draft-ready and
     attest-failure events each post ONE idempotent Today approval card to
     ACUTIS approval_gates via :18820; and the first cycle after 6am local
     stages ONE conveyor_daily_digest outbox event for the prior day (email
     remains behind the SOLVER_NOTIFY_EMAIL opt-in, default OFF).

  7. KNOWLEDGE-GRAPH LEG (scripts/export_obsidian.py): a registry hop that
     completed AND passed audit --strict refreshes the Obsidian vault notes
     on /Volumes/BCC-Storage (one note per PROVED module + honest index).
     Subprocess + timeout, content-hash idempotent, NEVER a cycle blocker —
     an unmounted or stalled USB vault is recorded and skipped.

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

try:  # package import (tests) vs script import (launchd) — same convention
    from aristotle import conveyor_notify  # type: ignore
except ImportError:
    import conveyor_notify  # type: ignore

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
    cross_file_timeout = os.environ.get("CROSS_TIMEOUT", "300")
    verify_budget = int(os.environ.get("CONVEYOR_VERIFY_BUDGET", "900"))
    cross_budget = int(os.environ.get("CONVEYOR_CROSS_BUDGET", "900"))
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
        # cloud axiom audit (AXLE #print axioms) — the soundness leg that promotes a
        # proof to registry PROVED now that local Lean cannot run on this box. Cloud
        # round-trips are seconds, but keep it NON-fatal so an AXLE outage records a
        # budget/error and the chain still advances (catalogue simply uses the prior
        # audit state; unaudited proofs stay PROVED_UNVERIFIED). Runs BEFORE
        # catalogue_domains so the same cycle can promote freshly-audited proofs.
        ("axle_axiom_audit", "axle_axiom_audit.py",
         {"AXLE_AXIOM_MAX": axle_max}, cross_budget, False),
        ("catalogue_domains", "catalogue_domains.py", {}, stage_timeout, True),
        ("lemma_mine", "lemma_mine.py", {}, stage_timeout, True),
        ("reduction_tracker", "reduction_tracker.py", {}, stage_timeout, True),
        # cross_check is the same shape as verify_stage: an independent axiom
        # audit whose LOCAL lake leg cannot clear the backlog in one cycle. It
        # persists per-file state (resumable) and is capped per run, so its
        # budget exhaustion is recorded but NON-fatal — a fatal timeout here
        # would freeze the whole chain (cursor never advances → the same
        # receipts reprocess forever → best_proofs churn → the audit never
        # drains). The truth gate is NOT weakened: catalogue_domains only
        # promotes a target to registry PROVED when cross_check reports
        # trusted=True for that exact content hash; until the audit lands a
        # proof stays at PROVED_UNVERIFIED. Per-file CROSS_TIMEOUT bounds a
        # single hung lake load so the run attempts several files per cycle.
        ("cross_check", "cross_check.py",
         {"CROSS_MAX": cross_max, "CROSS_TIMEOUT": cross_file_timeout},
         cross_budget, False),
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


# ------------------------------------------------- obsidian knowledge-graph leg

def run_obsidian_export(runner=None, timeout=None):
    """Vault knowledge-graph export (scripts/export_obsidian.py). Called ONLY
    after a registry hop that passed audit --strict (the caller guards), and
    NON-BLOCKING by construction: it runs as a subprocess with its own
    timeout, every outcome (including the vault being unmounted or the USB
    volume stalling) is recorded in the cycle and NEVER affects chain_ok,
    the cursor, or the attestation fingerprint. Kill switch:
    CONVEYOR_OBSIDIAN=0."""
    if os.environ.get("CONVEYOR_OBSIDIAN", "1") != "1":
        return {"ran": False, "note": "disabled via CONVEYOR_OBSIDIAN=0"}
    try:
        res = (runner or _run_repo_script)(
            "export_obsidian", ["scripts/export_obsidian.py"],
            timeout=int(timeout
                        or os.environ.get("CONVEYOR_OBSIDIAN_TIMEOUT", "300")))
        return {"ran": True, "status": res["status"],
                "tail": (res.get("tail") or "")[-300:]}
    except Exception as e:  # noqa: BLE001 — belt-and-braces: never blocks
        log(f"obsidian export failed (non-blocking): {e}")
        return {"ran": True, "status": "error", "tail": str(e)[:300]}


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


# ------------------------------------------------- paperclip spend attribution

PAPERCLIP_BASE = os.environ.get("CONVEYOR_PAPERCLIP_BASE", "http://127.0.0.1:3101")
# Riemann Labs (prefix RIE) — from the Paperclip company registry.
RIEMANN_COMPANY_ID = os.environ.get(
    "CONVEYOR_PAPERCLIP_COMPANY", "2305362b-28e3-4fa0-93b3-cc8eab3165f2")
REPO_PATH = "/Users/acutis/Projects/brockian-mathematics"

VERDICT_LINKS = (
    "Verdict evidence (local, honest — candidates are NOT registry-PROVED "
    "until verification passes):\n"
    f"- watcher verdicts per project uuid: {REPO_PATH}/aristotle/solver_state.json\n"
    f"- independent AXLE verdicts:        {REPO_PATH}/aristotle/axle_verify.json\n"
    f"- registry truth (post-audit only): {REPO_PATH}/registry/theorems.json\n"
    f"- provenance / verdict map:         {REPO_PATH}/provenance/verdicts.yaml"
)


def paperclip_issue_title(candidates):
    names = sorted({c["name"] for c in candidates})
    first = names[0] if names else "solver batch"
    extra = f" (+{len(names) - 1} more)" if len(names) > 1 else ""
    return f"Aristotle: {first}{extra} — candidate ready"


def build_paperclip_issue(ev, candidates):
    """One issue payload per digest batch: title from the project name(s),
    body = the candidates + verdict-evidence links + the receipt id (the
    idempotency key, stated in-band so the attribution is auditable)."""
    lines = [
        "Aristotle solver batch produced proof CANDIDATE(s) — spend attribution.",
        f"Receipt (idempotency key): {ev.get('receipt_id')}",
        "",
        "Candidates:",
    ]
    for c in candidates:
        lines.append(f"- [{c['account']}] {c['name']} — uuid {c['uuid'] or 'unknown'}")
    lines += ["", VERDICT_LINKS, "",
              "Next: the conveyor's verify/attest chain runs locally; the "
              "registry hop is gated on audit_registry_consistency --strict.",
              "Do NOT assign NOETHER (agent in error state); leave unassigned "
              "or assign TURING."]
    return {"title": paperclip_issue_title(candidates),
            "description": "\n".join(lines)}


def post_paperclip_issue(payload, base=None, company_id=None, opener=None):
    """POST one issue to Paperclip. Returns the created issue dict (contains
    id + identifier, e.g. RIE-276) or None on any failure. The endpoint was
    probed 2026-08-18: minimal {title, description} → 201; client-supplied
    originFingerprint/originKind are IGNORED by the server, so there is no
    server-side dedupe — callers must guard via conveyor_state."""
    url = (f"{base or PAPERCLIP_BASE}/api/companies/"
           f"{company_id or RIEMANN_COMPANY_ID}/issues")
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST",
    )
    try:
        with (opener or urllib.request.urlopen)(req, timeout=15) as r:
            body = r.read()
        issue = json.loads(body)
        if not isinstance(issue, dict) or not issue.get("id"):
            log("paperclip create returned unexpected body; treating as failure")
            return None
        return issue
    except Exception as e:  # noqa: BLE001
        log(f"paperclip issue create unavailable ({e}); will retry next cycle")
        return None


# Cap sized above the largest real backlog seen (142 receipts on 2026-08-18
# while :3101 was down); trimming past it permanently drops attributions
# because the cursor has already advanced, so it must never trim silently.
PENDING_PAPERCLIP_KEEP = 500


def _trim_pending_paperclip(pending):
    """Trim the retry queue to the cap, LOUDLY: anything trimmed here is an
    attribution permanently lost (the cursor is already past its receipt)."""
    kept = pending[-PENDING_PAPERCLIP_KEEP:]
    dropped = len(pending) - len(kept)
    if dropped:
        log(f"pending_paperclip over cap ({len(pending)} > "
            f"{PENDING_PAPERCLIP_KEEP}): PERMANENTLY dropping {dropped} "
            f"oldest undelivered attribution(s): "
            f"{[p.get('receipt_id') for p in pending[:dropped]]}")
    return kept


def _persist_state(state, state_path):
    """Per-POST durability. The Paperclip API has no dedupe, so the receipt
    guard must hit disk after EVERY successful POST: a hard kill (SIGKILL /
    power loss — this machine's known crash mode) mid-batch then re-posts at
    most the single in-flight issue whose success response was lost, never
    the whole batch. state_path is None in unit tests that exercise the pure
    guard logic without a state file."""
    if state_path:
        _atomic_json_dump(state, state_path)


def _record_paperclip_issue(issues, rid, res):
    issues[rid] = {"issue_id": res.get("id"),
                   "identifier": res.get("identifier"),
                   "created_at": _now()}
    log(f"paperclip attribution issue {res.get('identifier')} "
        f"for receipt {rid}")


def flush_pending_paperclip(state, poster=None, state_path=None):
    """Retry attribution issues queued while :3101 was down. The cursor may
    have advanced past their receipts (a successful chain does not wait for
    Paperclip), so this pending queue — not the outbox — is their only path
    to attribution. State is persisted to state_path immediately after EACH
    successful POST (the guard is checked before every POST, and a delivered
    item still sitting in the dumped pending list is dropped by that guard on
    reload), so a hard kill mid-flush can duplicate at most the single
    in-flight issue. Returns the number delivered."""
    poster = poster or post_paperclip_issue
    issues = state.setdefault("paperclip_issues", {})
    pending = state.get("pending_paperclip") or []
    still = []
    delivered = 0
    for item in pending:
        rid = item.get("receipt_id")
        if rid in issues:
            continue  # already filed elsewhere; drop
        res = poster(item.get("payload") or {})
        if res:
            _record_paperclip_issue(issues, rid, res)
            _persist_state(state, state_path)
            delivered += 1
        else:
            still.append(item)
    state["pending_paperclip"] = _trim_pending_paperclip(still)
    if delivered:
        _persist_state(state, state_path)  # drained pending list
    return delivered


def post_attribution_issues(state, digests, poster=None, state_path=None):
    """Per candidate batch, POST exactly one RIE issue. Idempotency: the API
    has no dedupe (verified — originFingerprint is ignored), so the guard is
    state["paperclip_issues"][receipt_id]; a receipt already recorded is NEVER
    re-posted, and state is persisted to state_path immediately after EACH
    successful POST — a hard kill mid-batch re-posts at most the one in-flight
    issue, never the whole batch. A failed POST queues the payload in
    state["pending_paperclip"] (retried every cycle even after the cursor
    advances past the receipt). Returns the number of issues created."""
    poster = poster or post_paperclip_issue
    issues = state.setdefault("paperclip_issues", {})
    pending = state.setdefault("pending_paperclip", [])
    created = 0
    for ev in digests:
        rid = ev.get("receipt_id")
        if not rid or rid in issues:
            continue
        if any(p.get("receipt_id") == rid for p in pending):
            continue  # already queued for retry
        cands = parse_candidates(ev.get("body", ""))
        if not cands:
            # a digest with no CANDIDATE entries attributes no spend; record
            # it so it is never re-examined as an issue source
            issues[rid] = {"skipped": "no candidates", "at": _now()}
            continue
        payload = build_paperclip_issue(ev, cands)
        res = poster(payload)
        if res:
            _record_paperclip_issue(issues, rid, res)
            _persist_state(state, state_path)
            created += 1
        else:
            pending.append({"receipt_id": rid, "payload": payload,
                            "queued_at": _now()})
            state["pending_paperclip"] = _trim_pending_paperclip(pending)
    return created


def proof_attempt_week(now=None):
    d = now or datetime.datetime.now(datetime.UTC)
    iso = d.isocalendar()
    return f"{iso[0]}-W{iso[1]:02d}"


def build_proof_attempt_issue(week):
    """The weekly replacement for the dead nightly hermes cron job
    (~/.hermes/cron/proof-attempt.json — never loaded by the hermes cron
    scheduler, which reads only cron/jobs.json; the file is now enabled:false).
    Hermes work flows through Paperclip attribution instead."""
    body = (
        f"Weekly proof-attempt request ({week}) — replaces the deprecated "
        "nightly 2am hermes cron job that targeted the old Desktop Lean path.\n\n"
        f"Target repo: {REPO_PATH}\n\n"
        "Task: find axiomatized results (grep for `axiom`/`sorry` in "
        "Brockian/*.lean), pick the most approachable one, attempt a proof, "
        "and verify with `lake build`. Record the outcome honestly: an "
        "attempt that does not compile is a FAILED attempt, never a claim.\n\n"
        "Truth gate: registry claims only change via scripts/gen_registry.py "
        "followed by scripts/audit_registry_consistency.py --strict.\n\n"
        "Do NOT assign NOETHER (agent in error state); leave unassigned or "
        "assign TURING."
    )
    return {"title": f"Aristotle: weekly proof attempt — {week}",
            "description": body}


def maybe_post_proof_attempt_request(state, poster=None, now=None,
                                     state_path=None):
    """File the weekly proof-attempt RIE issue at most once per ISO week.
    Guarded by state["proof_attempt_requests"][week], persisted to state_path
    immediately after a successful POST (no-dedupe API — see _persist_state);
    a failed POST records nothing so the next cycle retries. Returns True
    when an issue was filed."""
    poster = poster or post_paperclip_issue
    week = proof_attempt_week(now)
    done = state.setdefault("proof_attempt_requests", {})
    if week in done:
        return False
    res = poster(build_proof_attempt_issue(week))
    if not res:
        return False
    done[week] = {"issue_id": res.get("id"),
                  "identifier": res.get("identifier"), "created_at": _now()}
    _persist_state(state, state_path)
    log(f"weekly proof-attempt request filed: {res.get('identifier')} ({week})")
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


# ------------------------------------------------ publish + notify legs

PROVED_DRAFTS_KEEP = 100


def maybe_queue_proved_draft(state, cycle, before, after, poster=None,
                             card_poster=None, card_prober=None,
                             state_path=None):
    """When a completed registry hop changed the PROVED count, queue ONE
    Lovable showcase-update draft (via /queue-submit only — the manager's
    approval gate holds it) and post ONE Today approval card. Idempotent via
    a deterministic receipt over (before, after, new names) guarded in
    state["proved_drafts"]. Snapshots of None (unreadable registry) queue
    nothing — unknown is never treated as zero."""
    if state_path is None:
        state_path = STATE
    if not before or not after or after["count"] == before["count"]:
        return False
    new_names = sorted(after["names"] - before["names"])
    rid = conveyor_notify.draft_receipt_id(
        before["count"], after["count"], new_names)
    drafts = state.setdefault("proved_drafts", {})
    if rid in drafts:
        return False
    prompt = conveyor_notify.build_draft_prompt(before, after)
    queue_or_send_lovable(state, prompt, poster=poster)  # sent or queued: drafted
    drafts[rid] = {"at": _now(), "proved_before": before["count"],
                   "proved_after": after["count"],
                   "new_names": new_names[:40]}
    if len(drafts) > PROVED_DRAFTS_KEEP:
        state["proved_drafts"] = dict(
            list(drafts.items())[-PROVED_DRAFTS_KEEP:])
    cycle["lovable_drafts_queued"] = cycle.get("lovable_drafts_queued", 0) + 1
    _atomic_json_dump(state, state_path)
    log(f"proved-count draft queued: {before['count']} -> {after['count']} "
        f"({len(new_names)} new name(s)) receipt {rid}")
    if conveyor_notify.post_approval_card(
            state, rid,
            conveyor_notify.build_draft_ready_gate(rid, before, after,
                                                   new_names),
            poster=card_poster, prober=card_prober, state_path=state_path):
        cycle["approval_cards_posted"] = \
            cycle.get("approval_cards_posted", 0) + 1
    return True


DEFERRED_REASON = "verify_stage already running; deferred"


def maybe_post_attest_failure_card(state, cycle, fp,
                                   card_poster=None, card_prober=None,
                                   state_path=None):
    """One Today approval card per DISTINCT attest failure (chain stage
    failure or truth-gate stop). The receipt covers (reason, attest
    fingerprint) ONLY — deliberately not the digest receipts, which step 3
    consumes even when the registry hop fails — so the same failure retrying
    every 15 min posts exactly one card, including across the
    receipts-consumed boundary. A deferral behind an already-running
    verify_stage is not a failure."""
    if state_path is None:
        state_path = STATE
    reason = cycle.get("stopped_reason")
    if not reason or reason == DEFERRED_REASON:
        return False
    rid = conveyor_notify.attest_failure_receipt_id(reason, fp)
    detail = ""
    stages = cycle.get("stages") or []
    if stages:
        detail = stages[-1].get("tail") or ""
    posted = conveyor_notify.post_approval_card(
        state, rid, conveyor_notify.build_attest_failure_gate(rid, reason,
                                                              detail),
        poster=card_poster, prober=card_prober, state_path=state_path)
    if posted:
        cycle["approval_cards_posted"] = \
            cycle.get("approval_cards_posted", 0) + 1
    return posted


# ---------------------------------------------------------------- main cycle

def run_cycle():
    cursor = load_json(CURSOR, {})
    state = load_json(STATE, {})
    processed = set(cursor.get("processed_receipt_ids") or [])
    first_run = not os.path.exists(CURSOR)

    cycle = {"started_at": _now(), "new_receipts": 0, "candidates": [],
             "stages": [], "registry_hop": {"ran": False},
             "stopped_reason": None, "lovable_drafts_queued": 0,
             "approval_cards_posted": 0}

    # 0. retry lovable events queued while :18793 was down (cheap; every cycle)
    flushed = flush_pending_lovable(state)
    if flushed:
        cycle["lovable_flushed"] = flushed
        # Persist the drained pending list NOW: the heavy chain below can run
        # for hours, and a crash before the end-of-cycle dump would resurrect
        # already-delivered events next cycle (duplicate delivery).
        _atomic_json_dump(state, STATE)

    # 0b. retry Today approval cards queued while :18820 was down, then the
    # daily digest: ONE conveyor_daily_digest outbox event at the first cycle
    # after 6am local, covering the prior day (email stays behind the
    # SOLVER_NOTIFY_EMAIL opt-in inside solver_watch's dispatch path).
    cards_flushed = conveyor_notify.flush_pending_approval_cards(
        state, state_path=STATE)
    if cards_flushed:
        cycle["approval_cards_flushed"] = cards_flushed
    conveyor_notify.emit_daily_digest(state, state_path=STATE)

    # 1. read outbox from the cursor
    digests = new_digests(read_outbox_events(), processed)
    candidates = []
    for ev in digests:
        candidates.extend(parse_candidates(ev.get("body", "")))
    cycle["new_receipts"] = len(digests)
    cycle["candidates"] = candidates
    log(f"outbox: {len(digests)} new digest(s), {len(candidates)} candidate(s)")

    # 1b. spend attribution: one RIE Paperclip issue per candidate batch,
    # plus the weekly proof-attempt request. Guarded by receipt_id / ISO week
    # in state (the API has no dedupe). state_path=STATE makes the helpers
    # persist state after EVERY successful POST — a hard kill (SIGKILL /
    # power loss) mid-batch re-posts at most the single in-flight issue,
    # never the whole batch (the live first run was 142 sequential POSTs).
    pc_flushed = flush_pending_paperclip(state, state_path=STATE)
    filed = post_attribution_issues(state, digests, state_path=STATE)
    cycle["paperclip_issues_filed"] = filed + pc_flushed
    weekly = maybe_post_proof_attempt_request(state, state_path=STATE)
    if filed or pc_flushed or weekly:
        _atomic_json_dump(state, STATE)  # belt-and-suspenders + pending queue

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
    proved_before = conveyor_notify.registry_proved_snapshot()
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
            # PUBLISH LEG: a hop that changed the registry PROVED count queues
            # ONE showcase-update draft on the Lovable manager (approval-gated
            # there) + ONE Today approval card. Both are idempotent via a
            # deterministic receipt over (before, after, new names).
            proved_after = conveyor_notify.registry_proved_snapshot()
            maybe_queue_proved_draft(state, cycle, proved_before, proved_after)
            # KNOWLEDGE-GRAPH LEG: the registry just changed AND passed audit
            # --strict, so refresh the Obsidian vault notes. Guarded (only
            # here, never on an unchanged or failed hop) and non-blocking
            # (subprocess + timeout; a stalled USB vault is recorded, never
            # fatal — the export is content-hash idempotent so the next
            # successful run converges).
            cycle["obsidian_export"] = run_obsidian_export()
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

    # 4b. attest-failure Today card (one per distinct failure signature) +
    # fold this cycle into the daily-digest accumulator (observed counts only).
    maybe_post_attest_failure_card(state, cycle, fp)
    proved_now = conveyor_notify.registry_proved_snapshot()
    conveyor_notify.accumulate_daily_stats(
        state, cycle, proved_now["count"] if proved_now else None)

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
