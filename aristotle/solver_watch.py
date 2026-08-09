#!/usr/bin/env python3
"""
solver_watch.py — watch the Aristotle prover fleet across both accounts and
email one notification per solver when it PROVES or STOPS.

- Polls `aristotle list` for the admin key (ARISTOTLE_API_KEY) and the chris key
  (ARISTOTLE_API_KEY_CHRIS). Each project's NAME is *what it solves*.
- On the first run it records a baseline WITHOUT emailing (so you don't get a
  flood for jobs that were already finished). After that, every time a project
  transitions RUNNING -> IDLE (i.e. it finished), it downloads the result,
  checks whether the Lean is sorry-free, and emails:
      PROVED ✓   — finished, no `sorry`/`admit` left
      STOPPED    — finished but still has sorry/admit (Aristotle gave up on the
                   headline goal; supporting lemmas may still be proved)
- Also maintains solver_manifest.json — the live "what each system solves" view.

Email path: the running gmail bridge at :18799 (POST /api/gmail/send).
Recipient: $SOLVER_NOTIFY_TO (default chrisbrock54@gmail.com).

Idempotent + safe to run on a timer (launchd/cron every ~10 min).
"""
import json, os, re, subprocess, sys, tempfile, urllib.request, glob, datetime

HERE = os.path.dirname(os.path.abspath(__file__))
STATE = os.path.join(HERE, "solver_state.json")
MANIFEST = os.path.join(HERE, "solver_manifest.json")
LOG = os.path.join(HERE, "solver_watch.log")
GMAIL_SEND = "http://127.0.0.1:18799/send"
NOTIFY_TO = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")

ACCOUNTS = [
    ("admin", os.environ.get("ARISTOTLE_API_KEY")),
    ("chris", os.environ.get("ARISTOTLE_API_KEY_CHRIS")),
]


def log(msg):
    line = f"{datetime.datetime.now(datetime.UTC).isoformat()} {msg}"
    print(line)
    try:
        with open(LOG, "a") as fh:
            fh.write(line + "\n")
    except Exception:
        pass


def run_aristotle(args, key, timeout=180):
    env = dict(os.environ)
    if key:
        env["ARISTOTLE_API_KEY"] = key
    try:
        out = subprocess.run(
            ["uvx", "--from", "aristotlelib@latest", "aristotle", *args],
            capture_output=True, text=True, env=env, timeout=timeout,
        )
        return out.stdout
    except Exception as e:
        log(f"aristotle {args} failed: {e}")
        return ""


# Parse the fixed-width `list` table: ID(36) CREATED NAME STATUS
ROW = re.compile(
    r"^([0-9a-f]{8}-[0-9a-f-]{27,})\s+(.+?)\s{2,}(\S.*?)\s{2,}(RUNNING|IDLE)\s*$"
)


def list_projects(key):
    text = run_aristotle(["list", "--limit", "100"], key)
    rows = []
    for line in text.splitlines():
        m = ROW.match(line.rstrip())
        if m:
            rows.append(
                {"id": m.group(1), "created": m.group(2).strip(),
                 "name": m.group(3).strip(), "status": m.group(4)}
            )
    return rows


def verdict_for(pid, key):
    """Download the finished project and decide PROVED vs STOPPED."""
    d = tempfile.mkdtemp(prefix="arv_")
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
        return "PROVED", {"theorems": theorems, "sorries": 0}
    return "STOPPED", {"theorems": theorems, "sorries": sorries}


def send_email(subject, body):
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
    except Exception:
        return default


def main():
    state = load(STATE, {})           # id -> {account,name,status,notified,verdict}
    first_run = not os.path.exists(STATE)
    seen = {}
    manifest = []

    for account, key in ACCOUNTS:
        if not key:
            log(f"no key for account {account}; skipping")
            continue
        for p in list_projects(key):
            pid = p["id"]
            seen[pid] = True
            prev = state.get(pid, {})
            entry = {"account": account, "name": p["name"], "status": p["status"],
                     "created": p["created"], "notified": prev.get("notified", False),
                     "verdict": prev.get("verdict"),
                     "finished_at": prev.get("finished_at")}
            just_finished = (p["status"] == "IDLE") and (not entry["notified"])
            if just_finished and not first_run:
                verdict, meta = verdict_for(pid, key)
                entry["verdict"] = verdict
                entry["notified"] = True
                entry["finished_at"] = datetime.datetime.now(datetime.UTC).isoformat()
                icon = "✅ PROVED" if verdict == "PROVED" else (
                    "⏹️ STOPPED" if verdict == "STOPPED" else "☑️ FINISHED")
                subject = f"[Aristotle · {account}] {p['name']} — {icon}"
                body = (
                    f"Solver: {p['name']}\nAccount: {account}\nProject: {pid}\n"
                    f"Result: {verdict}\n"
                    + (f"Theorems: {meta.get('theorems')} · sorry left: {meta.get('sorries')}\n"
                       if 'theorems' in meta else f"{meta.get('note','')}\n")
                    + f"\nWhat it was solving: {p['name']} (see the Verified Frontier).\n"
                )
                send_email(subject, body)
            elif just_finished and first_run:
                # baseline: mark already-finished jobs notified, don't email
                entry["notified"] = True
                entry["verdict"] = entry.get("verdict") or "BASELINE"
            state[pid] = entry
            manifest.append({"id": pid, **{k: entry.get(k) for k in
                             ("account", "name", "status", "verdict", "created",
                              "finished_at")}})

    json.dump(state, open(STATE, "w"), indent=1)
    manifest.sort(key=lambda m: (m["status"] != "RUNNING", m["name"]))
    json.dump({"generated": datetime.datetime.now(datetime.UTC).isoformat(),
               "count": len(manifest), "solvers": manifest},
              open(MANIFEST, "w"), indent=1)
    _push_fleet_snapshot()

    running = sum(1 for m in manifest if m["status"] == "RUNNING")
    idle = sum(1 for m in manifest if m["status"] == "IDLE")
    log(f"poll done: {len(manifest)} solvers ({running} running, {idle} idle)"
        + (" [BASELINE — no emails sent this run]" if first_run else ""))
    if first_run:
        # one summary email so you know the watcher is live
        names = ", ".join(sorted({m["name"] for m in manifest})[:40])
        send_email(
            f"[Aristotle] Solver watch armed — {len(manifest)} solvers",
            f"Watching the Aristotle prover fleet across accounts {', '.join(a for a,_ in ACCOUNTS)}.\n"
            f"{running} running, {idle} idle right now.\n"
            f"From now on you'll get one email per solver when it PROVES or STOPS.\n\n"
            f"Currently tracking: {names}\n",
        )


if __name__ == "__main__":
    main()
