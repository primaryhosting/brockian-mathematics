#!/usr/bin/env python3
"""harvest_all.py — harvest EVERY finished (IDLE) Aristotle job on both accounts,
not just the ones night_submit tracked. This catches proofs submitted directly to
Aristotle (e.g. the Brockian serious-math program) that never went through the
pipeline and so were invisible to harvest_proofs.py.

For each IDLE project not already in harvest_ledger.json:
  - download + untar, read the .lean,
  - classify a sorry-free proof CANDIDATE (legacy internal token PROVED) vs STOPPED,
  - derive a target key from the proof's own `namespace`/`theorem` name (falls back
    to the project NAME, then the pid),
  - save candidates to harvest_100/<acct>_<id8>.lean and record them in the ledger.

Downstream select_best -> axle_verify then verify them with no further changes.
Resumable (skips pids already in the ledger). Paced. Read-only against Aristotle.
Env: HARVEST_ALL_MAX (default 200), HARVEST_ALL_PAGES (default 20 pages x100/acct).
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

ROOT = pathlib.Path(__file__).resolve().parent
OUT = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
LOCK = ROOT / ".harvest.lock"
NIGHT = ROOT / "submitted_night.json"
KEYENV = {"admin": "ARISTOTLE_API_KEY", "chris": "ARISTOTLE_API_KEY_CHRIS"}
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
UUID = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")
MAXDL = int(os.environ.get("HARVEST_ALL_MAX", "200"))
PAGES = int(os.environ.get("HARVEST_ALL_PAGES", "20"))
PINNED_ARISTOTLE_BIN = os.path.expanduser(
    "~/.local/share/aristotlelib-2.1.0/bin/aristotle"
)
ARISTOTLE_BIN = (
    os.environ.get("ARISTOTLE_BIN")
    or (PINNED_ARISTOTLE_BIN if os.path.isfile(PINNED_ARISTOTLE_BIN) else None)
    or shutil.which("aristotle")
)


def alist(key, pagkey=None):
    if not ARISTOTLE_BIN:
        return [], None
    args = [ARISTOTLE_BIN, "list",
            "--status", "IDLE", "--limit", "100"]
    if pagkey:
        args += ["--pagination-key", pagkey]
    e = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        r = subprocess.run(args, capture_output=True, text=True, env=e, timeout=120)
        out = (r.stdout or "") + "\n" + (r.stderr or "")  # pagination key prints to stderr
    except Exception:  # noqa: BLE001
        return [], None
    rows, nextk = [], None
    for l in out.splitlines():
        m = re.search(r"next page:\s*(\S+)", l)
        if m:
            nextk = m.group(1)
            continue
        s = l.strip()
        if UUID.match(s):
            pid = s[:36]
            # NAME sits between the CREATED column and the STATUS column
            rest = s[36:].rstrip()
            rest = re.sub(r"\bIDLE\s*$", "", rest).rstrip()
            name = re.sub(r"^\s*\d+\s+\w+\s+ago\s+", "", rest).strip()
            rows.append((pid, name))
    return rows, nextk


def all_idle(key):
    seen, pk = [], None
    for _ in range(PAGES):
        rows, pk = alist(key, pk)
        seen += rows
        if not pk or not rows:
            break
    # dedupe preserving order
    out, s = [], set()
    for pid, name in seen:
        if pid not in s:
            s.add(pid)
            out.append((pid, name))
    return out


def fetch(pid, key):
    if not ARISTOTLE_BIN:
        return False, None, ""
    d = tempfile.mkdtemp(prefix="harvall_")
    tar = os.path.join(d, f"{pid}.tar.gz")
    e = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        subprocess.run([ARISTOTLE_BIN, "download",
                        pid, "--destination", tar], capture_output=True, env=e, timeout=180)
        subprocess.run(["tar", "xzf", tar, "-C", d], capture_output=True, timeout=60)
    except Exception:  # noqa: BLE001
        return False, None, ""
    lean = ""
    for p in glob.glob(os.path.join(d, "**", "*.lean"), recursive=True):
        lean += open(p, errors="ignore").read() + "\n"
    if not lean.strip():
        return False, None, ""
    body = "\n".join(l for l in lean.splitlines() if not l.strip().startswith("--"))
    return True, ("STOPPED" if BAD.search(body) else "PROVED"), lean


def target_from(lean, name, pid):
    """Prefer the proof's own name: namespace (if any) + first theorem/lemma."""
    ns = None
    m = re.search(r"^\s*namespace\s+([\w.]+)", lean, re.M)
    if m:
        ns = m.group(1)
    t = re.search(r"^\s*(?:theorem|lemma)\s+([\w.]+)", lean, re.M)
    if t:
        return (ns + "." if ns and not t.group(1).startswith(ns) else "") + t.group(1)
    if name:
        return "Aristotle." + re.sub(r"[^A-Za-z0-9]+", "_", name).strip("_")[:80]
    return "Aristotle.job_" + pid[:8]


def main():
    lock_handle = LOCK.open("a+")
    try:
        fcntl.flock(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("harvest already running; skipped this overlapping poll")
        return
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    night = json.loads(NIGHT.read_text()) if NIGHT.exists() else {}
    # map pid -> pipeline target/tier so we keep good labels where we have them
    pid_meta = {}
    for tgt, v in night.items():
        for rec in v.get("ids", []):
            pid_meta[rec["project_id"]] = {"target": tgt, "tier": v.get("tier")}

    downloaded = 0
    new_proved = []
    for acct, env in KEYENV.items():
        key = os.environ.get(env)
        if not key:
            print(f"{acct}: no key, skip")
            continue
        idle = all_idle(key)
        todo = [(pid, nm) for pid, nm in idle if pid not in ledger]
        print(f"{acct}: {len(idle)} IDLE listed, {len(todo)} not yet harvested")
        for pid, name in todo:
            if downloaded >= MAXDL:
                break
            terminal, verdict, lean = fetch(pid, key)
            if not terminal:
                continue
            downloaded += 1
            meta = pid_meta.get(pid)
            target = meta["target"] if meta else target_from(lean, name, pid)
            tier = meta["tier"] if meta else ("Brockian-external" if "brock" in (name or "").lower()
                                              or "Brockian" in target else "External")
            if verdict == "PROVED":
                (OUT / f"{acct}_{pid[:8]}.lean").write_text(lean)
                new_proved.append((target, acct))
            ledger[pid] = {"target": target, "account": acct, "verdict": verdict,
                           "tier": tier, "origin": "list" if not meta else "pipeline",
                           "project_name": name}
            LEDGER.write_text(json.dumps(ledger, indent=1))
        if downloaded >= MAXDL:
            print(f"hit HARVEST_ALL_MAX={MAXDL}; stopping (rerun to continue)")
            break
    proved = sum(1 for v in ledger.values() if v.get("verdict") == "PROVED")
    print(f"\ndownloaded {downloaded} new | +{len(new_proved)} PROVED | ledger now {len(ledger)} ({proved} PROVED)")
    for t, a in new_proved[:40]:
        print(f"  PROVED {t} ({a})")


if __name__ == "__main__":
    main()
