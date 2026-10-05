#!/usr/bin/env python3
"""axle_verify.py — verify harvested proofs with AXLE (pinned cloud Lean + Mathlib).

The local `lake env lean` path pays a >2min import-Mathlib tax per file, so verify_stage
can't keep up. AXLE checks cloud-side in ~seconds with a strict verdict (sorry/admit =
hard fail), giving an INDEPENDENT verification leg fast enough to clear the backlog.
Verified results become the trust signal for catalogue + auto_pr.

Operates on best_proofs/ (deduped). Resumable via axle_verify.json. Capped + paced. The
verification machinery (normalize, content_hash, the AXLE compile check) lives in
`engine.verify`; this module is the harvest driver over best_proofs/.
"""
import glob
import json
import os
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from engine import verify as ev  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "best_proofs"
STATE = ROOT / "axle_verify.json"
MAX = int(os.environ.get("AXLE_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    files = sorted(glob.glob(str(SRC / "*.lean")))

    # re-check a file if it is new OR its content changed since last verification
    def stale(f):
        b = pathlib.Path(f).name
        if b not in state:
            return True
        if state[b].get("environment") != ev.DEFAULT_ENV:
            return True
        prev = state[b].get("hash")
        return prev is not None and prev != ev.content_hash(open(f, errors="ignore").read())

    todo = [f for f in files if stale(f)][:MAX]
    print(f"{len(files)} best proofs; AXLE-verifying {len(todo)} (cloud {ev.DEFAULT_ENV})")
    for f in todo:
        b = pathlib.Path(f).name
        raw = open(f, errors="ignore").read()
        try:
            r = ev.compile_check(raw)
            state[b] = {"verified": r.verified, "environment": r.environment,
                        "errors": r.errors[:2], "hash": ev.content_hash(raw)}
        except Exception as e:  # noqa: BLE001
            state[b] = {"verified": None, "error": str(e)[:200]}
        STATE.write_text(json.dumps(state, indent=1))
        v = state[b].get("verified")
        print(f"  {'OK ' if v else ('.. ' if v is None else 'xx ')} {b}"
              + ("" if v else f"  {state[b].get('errors') or state[b].get('error','')}"))
        time.sleep(PACE)
    verified = sum(1 for s in state.values() if s.get("verified") is True)
    failed = sum(1 for s in state.values() if s.get("verified") is False)
    print(f"\nAXLE-verified {verified} | failed {failed} | checked {len(state)}/{len(files)}")


if __name__ == "__main__":
    main()
