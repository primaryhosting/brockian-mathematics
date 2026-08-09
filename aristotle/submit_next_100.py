#!/usr/bin/env python3
"""Submit the next_100 proof queue to Aristotle across both accounts, in batches.

- Builds a real prompt per target (registry statement + module + goal), not a bare name.
- Submits via `uvx --from aristotlelib@latest aristotle submit` (the PATH 1.0.1 binary
  hits a dead /api/v2 endpoint). Async (no --wait); solver_watch polls results.
- Accounts: admin=$ARISTOTLE_API_KEY, chris=$ARISTOTLE_API_KEY_CHRIS (values never printed).
- Resumable: records (target,account)->project_id in submitted_ids.json; skips done.

Usage:
  python3 aristotle/submit_next_100.py --dry-run            # show what would be sent
  python3 aristotle/submit_next_100.py --limit 1            # live: submit 1 (validation)
  python3 aristotle/submit_next_100.py --batch 20           # live: all, 20 per batch, both accounts
  python3 aristotle/submit_next_100.py --tiers A1,D,C       # restrict to tiers
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent
QUEUE = ROOT / "next_100.json"
LEDGER = ROOT / "submitted_ids.json"
REGISTRY = ROOT.parent / "registry" / "theorems.json"

ACCOUNTS = [("admin", "ARISTOTLE_API_KEY"), ("chris", "ARISTOTLE_API_KEY_CHRIS")]


def load_registry_index():
    d = json.loads(REGISTRY.read_text())
    items = d if isinstance(d, list) else d.get("theorems") or next((v for v in d.values() if isinstance(v, list)), [])
    return {t.get("name"): t for t in items if isinstance(t, dict)}


def build_prompt(item, reg):
    r = reg.get(item["target"], {})
    stmt = r.get("statement")
    module = r.get("module") or ""
    lines = [f"Prove the following in Lean 4 (Mathlib), axiom-clean (no sorry/admit/native_decide):",
             f"Target: {item['target']}"]
    if stmt:
        lines.append(f"Statement:\n{stmt}")
    if module:
        lines.append(f"Module: {module}")
    lines.append(f"Goal: {item['goal']}")
    if item["tier"].startswith("A"):
        lines.append("This is a CONDITIONAL whose named hypothesis must be discharged to make it unconditional.")
    if item["tier"] == "D-pca-meta":
        lines.append("Formalize the stated soundness/completeness property of an SMT data-isolation model as a Lean theorem.")
    return "\n".join(lines)


def run_submit(prompt, key_env, dry):
    key = os.environ.get(key_env)
    if not key:
        return None, f"env {key_env} not set"
    if dry:
        return "DRY", None
    env = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        p = subprocess.run(["uvx", "--from", "aristotlelib@latest", "aristotle", "submit", prompt],
                           capture_output=True, text=True, env=env, timeout=300)
    except Exception as e:  # noqa: BLE001
        return None, f"exec error: {e}"
    out = (p.stdout or "") + (p.stderr or "")
    # extract a project id (uuid-ish token) from output
    import re
    m = re.search(r"[0-9a-f]{8}-?[0-9a-f]{4}", out) or re.search(r"\b([0-9a-f]{8,})\b", out)
    pid = m.group(0) if m else None
    return (pid or ("OK" if p.returncode == 0 else None)), (None if p.returncode == 0 else out[:400])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--batch", type=int, default=20)
    ap.add_argument("--tiers", default="")
    ap.add_argument("--accounts", default="admin,chris")
    args = ap.parse_args()

    reg = load_registry_index()
    queue = json.loads(QUEUE.read_text())["queue"]
    if args.tiers:
        want = tuple(args.tiers.split(","))
        queue = [q for q in queue if any(q["tier"].startswith(w) for w in want)]
    accounts = [(n, e) for (n, e) in ACCOUNTS if n in args.accounts.split(",")]
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}

    jobs = []
    for item in queue:
        for acct, env in accounts:
            k = f"{acct}:{item['target']}"
            if k in ledger:
                continue
            jobs.append((item, acct, env, k))
    if args.limit:
        jobs = jobs[:args.limit]

    print(f"{len(jobs)} submissions pending "
          f"({len(queue)} targets x {len(accounts)} accounts, minus {len(ledger)} already done)")
    if args.dry_run:
        for item, acct, env, k in jobs[:3]:
            print(f"\n--- [{acct}] {item['target']} ({item['tier']}) ---")
            print(build_prompt(item, reg)[:600])
        print(f"\n(dry-run) would submit {len(jobs)} jobs in batches of {args.batch}")
        return

    sent = 0
    for i, (item, acct, env, k) in enumerate(jobs):
        prompt = build_prompt(item, reg)
        pid, err = run_submit(prompt, env, dry=False)
        if pid:
            ledger[k] = {"project_id": pid, "tier": item["tier"], "account": acct}
            sent += 1
            print(f"[{i+1}/{len(jobs)}] {acct} {item['target']} -> {pid}")
        else:
            print(f"[{i+1}/{len(jobs)}] {acct} {item['target']} FAILED: {err}")
        LEDGER.write_text(json.dumps(ledger, indent=1))
        if (i + 1) % args.batch == 0:
            print(f"--- batch boundary ({i+1}) ---")
    print(f"\nDone. {sent} submitted this run. Ledger: {LEDGER}")


if __name__ == "__main__":
    main()
