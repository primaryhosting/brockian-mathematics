#!/usr/bin/env python3
"""axle_verify.py — verify harvested proofs with AXLE (pinned cloud Lean + Mathlib).

The local `lake env lean` path pays a >2min import-Mathlib tax per file, so
verify_stage can't keep up. AXLE checks cloud-side in ~seconds with a strict verdict
(sorry/admit = hard fail), giving us an INDEPENDENT verification leg fast enough to
clear the backlog. Verified results become the trust signal for catalogue + auto_pr.

Operates on best_proofs/ (deduped). Resumable via axle_verify.json. Capped + paced.
"""
import glob
import json
import os
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import axle_client as ax  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "best_proofs"
STATE = ROOT / "axle_verify.json"
MAX = int(os.environ.get("AXLE_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))


def normalize(content: str) -> str:
    """Aristotle output often has a comment header then a SECOND `import Mathlib`
    mid-file — a Lean syntax error. Hoist all imports (deduped) to the very top."""
    imports, body = [], []
    for l in content.splitlines():
        if l.strip().startswith("import "):
            if l.strip() not in imports:
                imports.append(l.strip())
        else:
            body.append(l)
    return "\n".join(imports + [""] + body)


def _hash(content: str) -> str:
    import hashlib
    return hashlib.sha256(content.encode()).hexdigest()[:16]


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    files = sorted(glob.glob(str(SRC / "*.lean")))
    # re-check a file if it is new OR its content changed since last verification
    # (so re-attacked / improved proofs get re-verified instead of staying cached).
    def stale(f):
        b = pathlib.Path(f).name
        if b not in state:
            return True
        if state[b].get("environment") != ax.DEFAULT_ENV:
            return True
        prev = state[b].get("hash")
        return prev is not None and prev != _hash(normalize(open(f, errors="ignore").read()))
    todo = [f for f in files if stale(f)][:MAX]
    print(f"{len(files)} best proofs; AXLE-verifying {len(todo)} (cloud {ax.DEFAULT_ENV})")
    for f in todo:
        b = pathlib.Path(f).name
        content = normalize(open(f, errors="ignore").read())
        try:
            r = ax.check(content)
            state[b] = {"verified": r.verified, "environment": r.environment,
                        "errors": r.errors[:2], "hash": _hash(content)}
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
