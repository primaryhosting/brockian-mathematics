#!/usr/bin/env python3
"""harvest_proofs.py — download finished Aristotle jobs by their FULL uuids.

Authoritative source: submitted_night.json {target: {ids:[{account,project_id,ts}]}}
(full uuids captured by night_submit). For each id not yet harvested, download under
that account's key, classify a sorry-free candidate (legacy token PROVED) vs STOPPED, and save candidates
to aristotle/harvest_100/<acct>_<id8>.lean so verify_stage can lake-verify them.

Empty download => still proving => retried next run. Resumable via harvest_ledger.json.
Emails a digest of newly-terminal results. No LLM calls; safe hourly.
"""
import glob
import fcntl
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
NIGHT = ROOT / "submitted_night.json"
OUT = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
LOCK = ROOT / ".harvest.lock"
REPORT = ROOT / "harvest_report.md"
NOTIFY = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")
KEYENV = {"admin": "ARISTOTLE_API_KEY", "chris": "ARISTOTLE_API_KEY_CHRIS"}
MAX = int(os.environ.get("HARVEST_MAX", "60"))
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
PINNED_ARISTOTLE_BIN = os.path.expanduser(
    "~/.local/share/aristotlelib-2.1.0/bin/aristotle"
)
ARISTOTLE_BIN = (
    os.environ.get("ARISTOTLE_BIN")
    or (PINNED_ARISTOTLE_BIN if os.path.isfile(PINNED_ARISTOTLE_BIN) else None)
    or shutil.which("aristotle")
)


def run(args, key, t=180):
    if not ARISTOTLE_BIN:
        return ""
    e = dict(os.environ)
    if key:
        e["ARISTOTLE_API_KEY"] = key
    try:
        return subprocess.run([ARISTOTLE_BIN, *args],
                              capture_output=True, text=True, env=e, timeout=t).stdout
    except Exception:  # noqa: BLE001
        return ""


def fetch(pid, key):
    d = tempfile.mkdtemp(prefix="harv_")
    tar = os.path.join(d, f"{pid}.tar.gz")
    run(["download", pid, "--destination", tar], key)
    lean = ""
    try:
        subprocess.run(["tar", "xzf", tar, "-C", d], capture_output=True, timeout=60)
        for p in glob.glob(os.path.join(d, "**", "*.lean"), recursive=True):
            lean += open(p, errors="ignore").read() + "\n"
    except Exception:  # noqa: BLE001
        pass
    if not lean.strip():
        return False, None, ""
    body = "\n".join(l for l in lean.splitlines() if not l.strip().startswith("--"))
    return True, ("STOPPED" if BAD.search(body) else "PROVED"), lean


def email(subj, body):
    try:
        payload = json.dumps({"to": NOTIFY, "subject": subj, "body": body}).encode()
        urllib.request.urlopen(urllib.request.Request("http://127.0.0.1:18799/send", data=payload,
                               headers={"Content-Type": "application/json"}), timeout=30).read()
    except Exception:  # noqa: BLE001
        pass


def main():
    lock_handle = LOCK.open("a+")
    try:
        fcntl.flock(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("harvest already running; skipped this overlapping poll")
        return
    OUT.mkdir(exist_ok=True)
    night = json.loads(NIGHT.read_text()) if NIGHT.exists() else {}
    harvested = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}

    jobs = []
    for target, v in night.items():
        for rec in v.get("ids", []):
            pid = rec["project_id"]
            if pid not in harvested:
                jobs.append((target, rec["account"], pid, v.get("tier")))

    newly = []
    for target, acct, pid, tier in jobs[:MAX]:
        key = os.environ.get(KEYENV.get(acct, ""))
        if not key:
            continue
        terminal, verdict, lean = fetch(pid, key)
        if not terminal:
            continue
        if verdict == "PROVED":
            (OUT / f"{acct}_{pid[:8]}.lean").write_text(lean)
        harvested[pid] = {"target": target, "account": acct, "verdict": verdict, "tier": tier}
        newly.append((target, acct, verdict))
        LEDGER.write_text(json.dumps(harvested, indent=1))

    proved = [h for h in harvested.values() if h["verdict"] == "PROVED"]
    total_ids = sum(len(v.get("ids", [])) for v in night.values())
    lines = [f"# Aristotle harvest — {len(harvested)}/{total_ids} resolved",
             f"- Proof candidates (legacy internal verdict `PROVED`; queued for independent verification): {len(proved)}",
             f"- STOPPED: {len(harvested)-len(proved)}",
             f"- still proving: {total_ids-len(harvested)}", "", "## Proof candidates"]
    for h in sorted(proved, key=lambda x: x["target"]):
        lines.append(f"- [{h['tier']}] {h['target']} ({h['account']})")
    REPORT.write_text("\n".join(lines))

    if newly:
        np = sum(1 for _, _, v in newly if v == "PROVED")
        email(f"[harvest] {np} new proofs, {len(harvested)}/{total_ids} resolved",
              f"newly resolved {len(newly)} ({np} PROVED). cumulative PROVED {len(proved)}.\n"
              + "\n".join(f"  {v} {t} ({a})" for t, a, v in newly[:40]))
    print(f"harvested {len(newly)} this run | cumulative {len(harvested)}/{total_ids} ({len(proved)} PROVED)")


if __name__ == "__main__":
    main()
