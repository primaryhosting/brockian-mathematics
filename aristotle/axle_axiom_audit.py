#!/usr/bin/env python3
"""axle_axiom_audit.py — independent AXIOM audit in the cloud (AXLE).

A proof can COMPILE yet smuggle in an extra axiom or a `sorryAx` (a hole Lean accepts
with only a warning). This runs the soundness audit CLOUD-side via AXLE: it resubmits
each AXLE-verified proof with `#print axioms <decls>` appended and reads the axiom set
back. A proof is `trusted` iff it compiles cleanly AND every audited declaration depends
only on the trusted kernel axioms {propext, Classical.choice, Quot.sound}, no `sorryAx`.

This is the audit that promotes a proof to registry PROVED (see catalogue_domains
`independent_ok`). It only audits proofs AXLE already verified — those are self-contained
(Mathlib-only), so the resubmission compiles cloud-side.

The verification machinery (normalize, content_hash, fully-qualified #print-axioms probe,
verdict) lives in `engine.verify`; this module is the harvest driver over best_proofs/.
Resumable via axle_axiom_audit.json, capped (AXLE_AXIOM_MAX) + paced (AXLE_PACE).
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
STATE = ROOT / "axle_axiom_audit.json"
AXLE_STATE = ROOT / "axle_verify.json"
MAX = int(os.environ.get("AXLE_AXIOM_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))


def _atomic_write(path: pathlib.Path, obj) -> None:
    """Write JSON via temp file + rename so a concurrent reader (catalogue_domains
    consumes this state in the live conveyor) never sees a half-written file."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=1))
    os.replace(tmp, path)


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    axle = json.loads(AXLE_STATE.read_text()) if AXLE_STATE.exists() else {}
    files = sorted(glob.glob(str(SRC / "*.lean")))

    def eligible(f):
        """Audit only AXLE-verified proofs; (re)audit when new or content changed."""
        b = pathlib.Path(f).name
        if axle.get(b, {}).get("verified") is not True:
            return False
        digest = ev.content_hash(open(f, errors="ignore").read())
        prev = state.get(b, {})
        return (prev.get("hash") != digest
                or prev.get("environment") != ev.DEFAULT_ENV
                or prev.get("trusted") is None)  # retry transient nulls

    todo = [f for f in files if eligible(f)][:MAX]
    print(f"{len(files)} best proofs; cloud axiom-auditing {len(todo)} "
          f"(AXLE {ev.DEFAULT_ENV})")
    for f in todo:
        b = pathlib.Path(f).name
        raw = open(f, errors="ignore").read()
        res = ev.axiom_audit(raw)
        rec = {"trusted": res["trusted"], "axioms": res["axioms"],
               "extra_axioms": res["extra_axioms"],
               "environment": res["environment"], "hash": ev.content_hash(raw)}
        if res["detail"]:
            rec["detail"] = res["detail"]
        state[b] = rec
        _atomic_write(STATE, state)
        mark = "OK " if res["trusted"] else (".. " if res["trusted"] is None else "xx ")
        print(f"  {mark}{b}  {rec.get('extra_axioms') or res['detail'] or 'kernel-clean'}")
        time.sleep(PACE)

    trusted = sum(1 for s in state.values() if s.get("trusted") is True)
    flagged = [b for b, s in state.items() if s.get("trusted") is False]
    print(f"\ncloud axiom-audited {len(state)} | kernel-trusted {trusted} | "
          f"FLAGGED {len(flagged)}: {flagged[:6]}")


if __name__ == "__main__":
    main()
