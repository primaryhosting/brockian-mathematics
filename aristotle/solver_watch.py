#!/usr/bin/env python3
"""
solver_watch.py — watch the Aristotle prover fleet across both accounts and
stage a notification when a solver yields a CANDIDATE or STOPS.

- Polls `aristotle list` for the admin key (ARISTOTLE_API_KEY) and the chris key
  (ARISTOTLE_API_KEY_CHRIS). Each project's NAME is *what it solves*.
- On the first run it records a baseline WITHOUT creating completion notices
  (so you don't get a flood for jobs that were already finished). After that,
  every time a project
  transitions RUNNING -> IDLE (i.e. it finished), it downloads the result,
  checks whether the Lean is sorry-free, and stages a consolidated digest:
      CANDIDATE ✓ — finished, no `sorry`/`admit` left; verification still required
      STOPPED    — finished but still has sorry/admit (Aristotle gave up on the
                   headline goal; supporting lemmas may still be proved)
- Also maintains solver_manifest.json — the live "what each system solves" view.

Notification path: an append-only local JSONL outbox. Email is disabled by
default and requires the explicit opt-in SOLVER_NOTIFY_EMAIL=1. When enabled,
the running Gmail bridge at :18799 is used for delivery and the result is
appended to the same audit journal.
Recipient when opted in: $SOLVER_NOTIFY_TO (default chrisbrock54@gmail.com).

Idempotent + safe to run on a timer (launchd/cron every ~10 min).
"""
import datetime
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
STATE = os.path.join(HERE, "solver_state.json")
MANIFEST = os.path.join(HERE, "solver_manifest.json")
LOG = os.path.join(HERE, "solver_watch.log")
OUTBOX = os.environ.get(
    "SOLVER_NOTIFICATION_OUTBOX",
    os.path.join(HERE, "solver_notification_outbox.jsonl"),
)
GMAIL_SEND = "http://127.0.0.1:18799/send"
NOTIFY_TO = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")
EMAIL_ENABLED = os.environ.get("SOLVER_NOTIFY_EMAIL", "").strip().lower() in {
    "1", "true", "yes", "on",
}

ACCOUNTS = [
    ("admin", os.environ.get("ARISTOTLE_API_KEY")),
    ("chris", os.environ.get("ARISTOTLE_API_KEY_CHRIS")),
]
PINNED_ARISTOTLE_BIN = os.path.expanduser(
    "~/.local/share/aristotlelib-2.1.0/bin/aristotle"
)
ARISTOTLE_BIN = (
    os.environ.get("ARISTOTLE_BIN")
    or (PINNED_ARISTOTLE_BIN if os.path.isfile(PINNED_ARISTOTLE_BIN) else None)
    or shutil.which("aristotle")
)
MAX_LIST_PAGES = int(os.environ.get("SOLVER_WATCH_PAGES", "50"))


def log(msg):
    line = f"{datetime.datetime.now(datetime.UTC).isoformat()} {msg}"
    print(line)
    try:
        with open(LOG, "a") as fh:
            fh.write(line + "\n")
    except Exception:
        pass


def run_aristotle(args, key, timeout=180):
    if not ARISTOTLE_BIN:
        log("aristotle executable not found; set ARISTOTLE_BIN")
        return None
    env = dict(os.environ)
    if key:
        env["ARISTOTLE_API_KEY"] = key
    try:
        out = subprocess.run(
            [ARISTOTLE_BIN, *args],
            capture_output=True, text=True, env=env, timeout=timeout,
        )
        combined = (out.stdout or "") + "\n" + (out.stderr or "")
        if out.returncode != 0:
            log(f"aristotle {args} exited {out.returncode}: {combined.strip()[:500]}")
            return None
        return combined
    except Exception as e:
        log(f"aristotle {args} failed: {e}")
        return None


# Parse the fixed-width `list` table: ID(36) CREATED NAME STATUS
ROW = re.compile(
    r"^([0-9a-f]{8}-[0-9a-f-]{27,})\s+(.+?)\s{2,}(\S.*?)\s{2,}(RUNNING|IDLE)\s*$"
)


def list_projects(key):
    rows = []
    pagination_key = None
    for _ in range(MAX_LIST_PAGES):
        args = ["list", "--limit", "100"]
        if pagination_key:
            args += ["--pagination-key", pagination_key]
        page = run_aristotle(args, key)
        if page is None:
            return None
        next_key = None
        for line in page.splitlines():
            key_match = re.search(r"next page:\s*(\S+)", line)
            if key_match:
                next_key = key_match.group(1)
                continue
            m = ROW.match(line.rstrip())
            if m:
                rows.append(
                    {"id": m.group(1), "created": m.group(2).strip(),
                     "name": m.group(3).strip(), "status": m.group(4)}
                )
        if not next_key:
            break
        pagination_key = next_key
    else:
        log(f"WARNING: account listing truncated at {MAX_LIST_PAGES} pages "
            f"({len(rows)} rows); raise SOLVER_WATCH_PAGES")
    return rows


def verdict_for(pid, key):
    """Download the finished project and decide CANDIDATE vs STOPPED."""
    d = tempfile.mkdtemp(prefix="arv_")
    try:
        tar = os.path.join(d, f"{pid}.tar.gz")
        run_aristotle(["download", pid, "--destination", tar], key, timeout=180)
        lean = ""
        try:
            subprocess.run(["tar", "xzf", tar, "-C", d], capture_output=True, timeout=60)
            for p in glob.glob(os.path.join(d, "**", "*.lean"), recursive=True):
                lean += open(p, errors="ignore").read() + "\n"
        except Exception as e:
            log(f"verdict extract {pid} failed: {e}")
        if not lean:
            return "FINISHED", {"note": "result not downloadable; status only"}
        # strip line comments so `-- sorry` doesn't count
        code = re.sub(r"--[^\n]*", "", lean)
        sorries = len(re.findall(r"\bsorry\b", code)) + len(re.findall(r"\badmit\b", code))
        theorems = len(re.findall(r"\b(theorem|lemma)\b", code))
        if sorries == 0 and theorems > 0:
            return "CANDIDATE", {"theorems": theorems, "sorries": 0,
                                 "note": "sorry-free Aristotle output; independent verification pending"}
        return "STOPPED", {"theorems": theorems, "sorries": sorries}
    finally:
        shutil.rmtree(d, ignore_errors=True)


def _atomic_json_dump(obj, path, indent=1):
    """Write JSON to a temp file, fsync, then rename into place.

    On ENOSPC (a documented failure mode on this machine) the dump raises
    against the .tmp file and the prior good file is preserved."""
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh, indent=indent)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def _append_outbox_event(event):
    os.makedirs(os.path.dirname(os.path.abspath(OUTBOX)), exist_ok=True)
    with open(OUTBOX, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(event, sort_keys=True, ensure_ascii=False) + "\n")
        fh.flush()
        os.fsync(fh.fileno())


def _read_outbox_events():
    events = []
    try:
        with open(OUTBOX, encoding="utf-8") as fh:
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


def _outbox_has_receipt(receipt_id):
    return any(
        event.get("receipt_id") == receipt_id
        and event.get("event") == "notification.staged"
        for event in _read_outbox_events()
    )


def _email_delivery_succeeded(receipt_id):
    return any(
        event.get("receipt_id") == receipt_id
        and event.get("event") == "notification.email_delivery"
        and event.get("status") == "succeeded"
        for event in _read_outbox_events()
    )


def stage_notification(subject, body, kind="solver_completion_digest"):
    """Durably stage one deterministic, locally auditable notification."""
    canonical = json.dumps(
        {"kind": kind, "subject": subject, "body": body},
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    receipt_id = "aristotle_notice_" + hashlib.sha256(canonical).hexdigest()[:24]
    if not _outbox_has_receipt(receipt_id):
        _append_outbox_event({
            "schema": "acutis.aristotle.notification.v1",
            "event": "notification.staged",
            "receipt_id": receipt_id,
            "created_at": datetime.datetime.now(datetime.UTC).isoformat(),
            "kind": kind,
            "subject": subject,
            "body": body,
            "channel": "local_outbox",
        })
        log(f"notification staged locally: {receipt_id}")
    else:
        log(f"notification already staged: {receipt_id}")
    return receipt_id


def send_email(subject, body):
    if not EMAIL_ENABLED:
        log("email delivery disabled; set SOLVER_NOTIFY_EMAIL=1 to opt in")
        return False
    payload = json.dumps({"to": NOTIFY_TO, "subject": subject, "body": body}).encode()
    req = urllib.request.Request(
        GMAIL_SEND, data=payload, headers={"Content-Type": "application/json"}
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            r.read()
        log(f"emailed: {subject}")
        return True
    except Exception as e:
        log(f"email FAILED ({subject}): {e}")
        return False


def _deliver_and_record(receipt_id, subject, body):
    """Attempt email delivery and append the delivery-audit event."""
    succeeded = send_email(subject, body)
    _append_outbox_event({
        "schema": "acutis.aristotle.notification.v1",
        "event": "notification.email_delivery",
        "receipt_id": receipt_id,
        "created_at": datetime.datetime.now(datetime.UTC).isoformat(),
        "channel": "email",
        "recipient": NOTIFY_TO,
        "status": "succeeded" if succeeded else "failed",
    })
    return succeeded


def dispatch_notification(subject, body, kind="solver_completion_digest"):
    """Stage locally, then optionally deliver by email under explicit opt-in."""
    receipt_id = stage_notification(subject, body, kind=kind)
    if not EMAIL_ENABLED:
        return {"receipt_id": receipt_id, "email": "disabled"}
    if _email_delivery_succeeded(receipt_id):
        log(f"email delivery already succeeded: {receipt_id}")
        return {"receipt_id": receipt_id, "email": "already_succeeded"}
    succeeded = _deliver_and_record(receipt_id, subject, body)
    return {
        "receipt_id": receipt_id,
        "email": "succeeded" if succeeded else "failed",
    }


def retry_failed_emails(limit=10):
    """Re-deliver staged digests whose LATEST email delivery attempt failed.

    Only receipts whose most recent notification.email_delivery event has
    status "failed" are retried (events are appended chronologically, so the
    last one wins). Receipts with NO delivery event were staged while email
    was opted out and are deliberately never blasted out as backlog.
    """
    if not EMAIL_ENABLED:
        return
    staged = {}
    latest_status = {}
    for event in _read_outbox_events():
        rid = event.get("receipt_id")
        if not rid:
            continue
        if event.get("event") == "notification.staged":
            staged[rid] = (event.get("subject") or "", event.get("body") or "")
        elif event.get("event") == "notification.email_delivery":
            latest_status[rid] = event.get("status")
    retried = 0
    for rid, status in latest_status.items():
        if status != "failed" or rid not in staged:
            continue
        if retried >= limit:
            log(f"email retry limit ({limit}) reached; remaining failed digests "
                "will be retried on a later poll")
            break
        subject, body = staged[rid]
        log(f"retrying failed email delivery: {rid} ({subject})")
        ok = _deliver_and_record(rid, subject, body)
        log(f"email retry {'succeeded' if ok else 'failed'}: {rid}")
        retried += 1


def _push_fleet_snapshot() -> None:
    try:
        script = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "push_fleet_snapshot.py")
        subprocess.run([sys.executable, script], timeout=60, check=False)
    except Exception as e:
        log(f"fleet snapshot push failed (non-fatal): {e}")


def load(path, default):
    try:
        return json.load(open(path))
    except FileNotFoundError:
        return default
    except Exception as e:
        # A present-but-unparseable file is a real problem (e.g. a torn write
        # from a crash) — surface it instead of silently resetting state.
        log(f"WARNING: {path} exists but failed to parse ({e}); using default")
        return default


def main():
    # Heal digests whose email delivery failed during an earlier poll (e.g. a
    # gmail-bridge outage) even if this poll has no new completions.
    retry_failed_emails()
    state = load(STATE, {})           # id -> {account,name,status,notified,verdict}
    # Historical watcher versions called a sorry-free download PROVED before the
    # independent verification leg. Correct that vocabulary in place.
    migrated = 0
    for record in state.values():
        if record.get("verdict") == "PROVED":
            record["verdict"] = "CANDIDATE"
            migrated += 1
    if migrated:
        log(f"migrated {migrated} legacy watcher verdicts PROVED -> CANDIDATE")
    first_run = not os.path.exists(STATE)
    seen = {}
    manifest = []
    completed = []

    successful_accounts = 0
    for account, key in ACCOUNTS:
        if not key:
            log(f"no key for account {account}; skipping")
            continue
        projects = list_projects(key)
        if projects is None:
            log(f"account {account} poll failed; preserving prior state")
            continue
        successful_accounts += 1
        for p in projects:
            pid = p["id"]
            seen[pid] = True
            prev = state.get(pid, {})
            entry = {"account": account, "name": p["name"], "status": p["status"],
                     "created": p["created"], "notified": prev.get("notified", False),
                     "verdict": prev.get("verdict"),
                     "finished_at": prev.get("finished_at")}
            just_finished = (
                prev.get("status") == "RUNNING"
                and p["status"] == "IDLE"
                and not entry["notified"]
            )
            if just_finished and not first_run:
                verdict, meta = verdict_for(pid, key)
                entry["verdict"] = verdict
                entry["notified"] = True
                entry["finished_at"] = datetime.datetime.now(datetime.UTC).isoformat()
                icon = "🧪 CANDIDATE" if verdict == "CANDIDATE" else (
                    "⏹️ STOPPED" if verdict == "STOPPED" else "☑️ FINISHED")
                body = (
                    f"Solver: {p['name']}\nAccount: {account}\nProject: {pid}\n"
                    f"Result: {verdict}\n"
                    + (f"Theorems: {meta.get('theorems')} · sorry left: {meta.get('sorries')}\n"
                       if 'theorems' in meta else f"{meta.get('note','')}\n")
                    + f"\nWhat it was solving: {p['name']} (see the Verified Frontier).\n"
                )
                completed.append((icon, p["name"], account, body))
            elif p["status"] == "IDLE" and not prev:
                # A newly discovered historical IDLE project is baseline, not a
                # RUNNING -> IDLE transition. Never download/notify the backlog.
                entry["notified"] = True
                entry["verdict"] = entry.get("verdict") or "BASELINE"
            state[pid] = entry
            manifest.append({"id": pid, **{k: entry.get(k) for k in
                             ("account", "name", "status", "verdict", "created",
                              "finished_at")}})

    if successful_accounts == 0:
        log("poll aborted: no Aristotle account completed successfully; state preserved")
        return

    manifest.sort(key=lambda m: (m["status"] != "RUNNING", m["name"]))
    _atomic_json_dump({"generated": datetime.datetime.now(datetime.UTC).isoformat(),
                       "count": len(manifest), "solvers": manifest}, MANIFEST)
    _push_fleet_snapshot()

    running = sum(1 for m in manifest if m["status"] == "RUNNING")
    idle = sum(1 for m in manifest if m["status"] == "IDLE")

    if completed:
        candidates = sum(1 for icon, *_ in completed if "CANDIDATE" in icon)
        stopped = sum(1 for icon, *_ in completed if "STOPPED" in icon)
        lines = [
            f"{len(completed)} Aristotle projects completed in this poll.",
            f"Proof candidates: {candidates} · stopped: {stopped}",
            "Candidates are not registry-PROVED until local/AXLE verification passes.",
            "",
        ]
        for icon, name, account, body in completed[:80]:
            lines.append(f"{icon} [{account}] {name}")
            project = re.search(r"^Project: (.+)$", body, re.M)
            if project:
                lines.append(f"  {project.group(1)}")
        dispatch_notification(
            f"[Aristotle] {len(completed)} completions — {candidates} candidates, {stopped} stopped",
            "\n".join(lines),
        )

    if first_run:
        # Stage one summary so the watcher activation is locally auditable.
        names = ", ".join(sorted({m["name"] for m in manifest})[:40])
        dispatch_notification(
            f"[Aristotle] Solver watch armed — {len(manifest)} solvers",
            f"Watching the Aristotle prover fleet across accounts {', '.join(a for a,_ in ACCOUNTS)}.\n"
            f"{running} running, {idle} idle right now.\n"
            f"Completion digests will be staged in the local notification outbox.\n\n"
            f"Currently tracking: {names}\n",
            kind="solver_watch_armed",
        )

    # A completion becomes `notified`, and a first-run baseline becomes armed,
    # only after its notice is durably present in the local outbox. If staging
    # raises, the prior state remains on disk and the next poll safely retries.
    _atomic_json_dump(state, STATE)
    log(f"poll done: {len(manifest)} solvers ({running} running, {idle} idle)"
        + (" [BASELINE — no completion digest delivered]" if first_run else ""))


if __name__ == "__main__":
    main()
