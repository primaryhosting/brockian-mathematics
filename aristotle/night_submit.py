#!/usr/bin/env python3
"""night_submit.py — drip paced proof batches to Aristotle all night, both accounts.

Fixes the earlier over-count: records ONLY full uuids (a submit that returns no uuid
or a rate-limit signal is a FAILURE, retried next cycle — never logged as success).
Paced (sleep between submits) + backs off on rate-limit so we don't trip the burst
limit that dropped ~170 of the first run.

Each cycle (driven by the LaunchAgent every ~20 min): pick BATCH targets with the
fewest attempts (tractable tiers first), submit each to BOTH accounts, record full
ids in submitted_night.json {target: {attempts, ids:[{account,project_id,ts}]}}.
Round-robins the open frontier so Aristotle keeps re-attacking it (it's stochastic —
more attempts = more chances). Night window + nightly cap as safety backstops.

Env: BATCH (default 8), PACE_S (5), NIGHT_START (18), NIGHT_END (9), NIGHT_CAP (600).
"""
import datetime
import json
import os
import pathlib
import re
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
QUEUES = os.environ.get("QUEUES", "next_100.json,domains_queue.json,mined_queue.json").split(",")
REG = REPO / "registry" / "theorems.json"
LEDGER = ROOT / "submitted_night.json"
LOG = ROOT / "night_submit.log"
UUID = re.compile(r"\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b")
RATE = re.compile(r"429|rate.?limit|too many|quota", re.I)
ACCOUNTS = [("admin", "ARISTOTLE_API_KEY"), ("chris", "ARISTOTLE_API_KEY_CHRIS")]
BATCH = int(os.environ.get("BATCH", "8"))
PACE = float(os.environ.get("PACE_S", "5"))
NIGHT_START = int(os.environ.get("NIGHT_START", "18"))
NIGHT_END = int(os.environ.get("NIGHT_END", "9"))
NIGHT_CAP = int(os.environ.get("NIGHT_CAP", "600"))
TIER_RANK = {"A1-discharge-literature": 0, "D-pca-meta": 1, "C-corpus-extension": 2,
             "A2-discharge-open": 3, "B-conjecture": 4}


def log(m):
    line = f"{datetime.datetime.now().isoformat(timespec='seconds')} {m}"
    with open(LOG, "a") as f:
        f.write(line + "\n")
    print(line)


def in_window():
    h = datetime.datetime.now().hour
    return h >= NIGHT_START or h < NIGHT_END


def reg_index():
    d = json.loads(REG.read_text())
    items = d if isinstance(d, list) else d.get("theorems") or next((v for v in d.values() if isinstance(v, list)), [])
    return {t["name"]: t for t in items if isinstance(t, dict) and "name" in t}


def prompt_for(item, reg):
    r = reg.get(item["target"], {})
    stmt = item.get("statement") or r.get("statement")
    parts = ["Prove in Lean 4 (Mathlib), axiom-clean (no sorry/admit/native_decide):",
             f"Target: {item['target']}"]
    if stmt:
        parts.append("Statement:\n" + stmt)
    if r.get("module"):
        parts.append("Module: " + r["module"])
    parts.append("Goal: " + item["goal"])
    if item["tier"].startswith("A"):
        parts.append("Discharge the named hypothesis to make it unconditional.")
    return "\n".join(parts)


def submit(prompt, key):
    env = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        p = subprocess.run(["uvx", "--from", "aristotlelib@latest", "aristotle", "submit", prompt],
                           capture_output=True, text=True, env=env, timeout=300)
    except Exception as e:  # noqa: BLE001
        return None, f"exec:{e}"
    out = (p.stdout or "") + (p.stderr or "")
    if RATE.search(out):
        return None, "RATE"
    m = UUID.search(out)
    return (m.group(0) if m else None), (None if m else out[:200])


def main():
    if not in_window():
        log(f"outside night window [{NIGHT_START}:00-{NIGHT_END}:00]; skip")
        return
    reg = reg_index()
    queue = []
    for qf in QUEUES:
        p = ROOT / qf.strip()
        if p.exists():
            d = json.loads(p.read_text())
            queue += d["queue"] if isinstance(d, dict) else d
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    total_ids = sum(len(v.get("ids", [])) for v in ledger.values())
    if total_ids >= NIGHT_CAP:
        log(f"nightly cap {NIGHT_CAP} reached ({total_ids}); skip"); return

    def attempts(t):
        return len(ledger.get(t["target"], {}).get("ids", []))
    order = sorted(queue, key=lambda t: (attempts(t), t.get("rank", TIER_RANK.get(t["tier"], 9))))
    picks = order[:BATCH]

    sent = fails = 0
    for item in picks:
        pr = prompt_for(item, reg)
        for acct, envname in ACCOUNTS:
            key = os.environ.get(envname)
            if not key:
                continue
            pid, err = submit(pr, key)
            if pid:
                e = ledger.setdefault(item["target"], {"tier": item["tier"], "ids": []})
                e["ids"].append({"account": acct, "project_id": pid,
                                 "ts": datetime.datetime.now().isoformat(timespec="seconds")})
                sent += 1
                log(f"OK {acct} {item['target']} -> {pid}")
            else:
                fails += 1
                log(f"FAIL {acct} {item['target']} ({err})")
                if err == "RATE":
                    log("rate-limited; ending cycle early (back off to next interval)")
                    LEDGER.write_text(json.dumps(ledger, indent=1))
                    return
            LEDGER.write_text(json.dumps(ledger, indent=1))
            time.sleep(PACE)
        if fails >= 4:
            log("too many failures; ending cycle"); break
    log(f"cycle done: sent={sent} fails={fails} cumulative_ids={total_ids+sent}/{NIGHT_CAP}")


if __name__ == "__main__":
    main()
