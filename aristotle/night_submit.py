#!/usr/bin/env python3
"""Drip-paced Aristotle submissions across both configured accounts.

The tracked ``PAUSE_SUBMISSIONS`` sentinel is a hard operational gate. Harvest and
verification jobs do not consult it, so a consolidation pause stops only new generic
submissions. A successful submission is recorded only when the CLI returns a full UUID.
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
PAUSE_FILE = ROOT / "PAUSE_SUBMISSIONS"
QUEUES = os.environ.get(
    "QUEUES",
    "next_100.json,domains_queue.json,mined_queue.json,pca_lean_queue.json,"
    "frontier_queue.json,frontier2.json,reattack_queue.json,frontier_spectral.json,"
    "frontier_betrothed_queue.json,frontier_linalg.json,frontier_riemann.json,"
    "frontier_rh2.json,frontier_primes.json,frontier_fibonacci.json,"
    "frontier_infinity.json,frontier_wave2.json,frontier_wave3.json,"
    "frontier_wave4.json,frontier_wave5.json",
).split(",")
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
TIER_RANK = {
    "A1-discharge-literature": 0,
    "D-pca-meta": 1,
    "C-corpus-extension": 2,
    "A2-discharge-open": 3,
    "B-conjecture": 4,
}


def log(message):
    line = f"{datetime.datetime.now().isoformat(timespec='seconds')} {message}"
    with open(LOG, "a") as handle:
        handle.write(line + "\n")
    print(line)


def in_window():
    hour = datetime.datetime.now().hour
    return hour >= NIGHT_START or hour < NIGHT_END


def reg_index():
    data = json.loads(REG.read_text())
    items = data if isinstance(data, list) else data.get("theorems") or next(
        (value for value in data.values() if isinstance(value, list)), []
    )
    return {item["name"]: item for item in items if isinstance(item, dict) and "name" in item}


def prompt_for(item, registry, attempt=0):
    import strategy
    import titles

    record = registry.get(item["target"], {})
    statement = item.get("statement") or record.get("statement")
    tier = item.get("tier", "")
    human = titles.title(item["target"], tier)
    header = titles.header(item["target"], tier, None, verified=False)
    parts = [
        human,
        "Prove in Lean 4 (Mathlib), without sorry/admit/native_decide or added axioms:",
        f"Target: {item['target']}",
        "BEGIN your Lean file with EXACTLY this header comment (then the proof):",
        header,
    ]
    if statement:
        parts.append("Statement:\n" + statement)
    if record.get("module"):
        parts.append("Module: " + record["module"])
    parts.append("Goal: " + item["goal"])
    if item["tier"].startswith("A"):
        parts.append("Discharge the named hypothesis to make it unconditional.")
    hint = strategy.pick(attempt)
    if hint:
        parts.append("Approach: " + hint)
    return "\n".join(parts)


def _stat_safe(prompt):
    encoded = prompt.encode()
    return len(encoded) < 1000 and all(len(segment.encode()) < 250 for segment in prompt.split("/"))


def submit(prompt, key):
    env = dict(os.environ, ARISTOTLE_API_KEY=key)
    tmp = None
    if _stat_safe(prompt):
        args = ["uvx", "--from", "aristotlelib@latest", "aristotle", "submit", prompt]
    else:
        import tempfile

        tmp = tempfile.mkdtemp(prefix="arsub_")
        pathlib.Path(tmp, "INSTRUCTIONS.md").write_text(prompt)
        short = (
            "Read INSTRUCTIONS.md and prove the stated target. Output Lean 4 (Mathlib) "
            "without sorry/admit/native_decide or added axioms."
        )
        args = [
            "uvx",
            "--from",
            "aristotlelib@latest",
            "aristotle",
            "submit",
            short,
            "--project-dir",
            tmp,
        ]
    try:
        process = subprocess.run(args, capture_output=True, text=True, env=env, timeout=300)
    except Exception as exc:  # noqa: BLE001
        return None, f"exec:{exc}"
    finally:
        if tmp:
            import shutil

            shutil.rmtree(tmp, ignore_errors=True)
    output = (process.stdout or "") + (process.stderr or "")
    if RATE.search(output):
        return None, "RATE"
    match = UUID.search(output)
    return (match.group(0) if match else None), (None if match else output[:200])


def main():
    if PAUSE_FILE.exists():
        log(f"submissions paused by {PAUSE_FILE}; skip")
        return
    if not in_window():
        log(f"outside night window [{NIGHT_START}:00-{NIGHT_END}:00]; skip")
        return

    registry = reg_index()
    queue = []
    for queue_name in QUEUES:
        path = ROOT / queue_name.strip()
        if path.exists():
            data = json.loads(path.read_text())
            queue += data["queue"] if isinstance(data, dict) else data

    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    total_ids = sum(len(value.get("ids", [])) for value in ledger.values())
    if total_ids >= NIGHT_CAP:
        log(f"submission cap {NIGHT_CAP} reached ({total_ids}); skip")
        return

    def attempts(item):
        return len(ledger.get(item["target"], {}).get("ids", []))

    order = sorted(
        queue,
        key=lambda item: (attempts(item), item.get("rank", TIER_RANK.get(item["tier"], 9))),
    )
    picks = order[:BATCH]
    sent = fails = 0
    for item in picks:
        prompt = prompt_for(item, registry, attempts(item))
        for account, env_name in ACCOUNTS:
            key = os.environ.get(env_name)
            if not key:
                continue
            project_id, error = submit(prompt, key)
            if project_id:
                entry = ledger.setdefault(item["target"], {"tier": item["tier"], "ids": []})
                entry["ids"].append(
                    {
                        "account": account,
                        "project_id": project_id,
                        "ts": datetime.datetime.now().isoformat(timespec="seconds"),
                    }
                )
                sent += 1
                log(f"OK {account} {item['target']} -> {project_id}")
            else:
                fails += 1
                log(f"FAIL {account} {item['target']} ({error})")
                if error == "RATE":
                    log("rate-limited; ending cycle early")
                    LEDGER.write_text(json.dumps(ledger, indent=1))
                    return
            LEDGER.write_text(json.dumps(ledger, indent=1))
            time.sleep(PACE)
        if fails >= 4:
            log("too many failures; ending cycle")
            break
    log(f"cycle done: sent={sent} fails={fails} cumulative_ids={total_ids + sent}/{NIGHT_CAP}")


if __name__ == "__main__":
    main()
