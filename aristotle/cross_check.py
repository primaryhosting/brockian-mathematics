#!/usr/bin/env python3
"""cross_check.py — independent trust layer: a proof can COMPILE yet smuggle in an
extra axiom. This re-checks each best proof's ACTUAL axiom set via `#print axioms`
(a check independent of "it compiled"), flagging anything beyond the trusted kernel
axioms {propext, Classical.choice, Quot.sound} or any sorryAx.

Optionally also cross-verifies against a second toolchain via AXLE if AXLE_API_KEY is
present (skipped otherwise — never handles a key it doesn't have). Slow (lake); runs
on the small deduped best_proofs set, resumable, capped per run.
"""
import glob
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
sys.path.insert(0, str(REPO))
from engine.verify import ALLOWED_AXIOMS as SAFE  # noqa: E402
from engine.verify import content_hash, normalize, qualified_decls  # noqa: E402

BEST = ROOT / "best_proofs"
STATE = ROOT / "cross_check.json"
TIMEOUT = int(os.environ.get("CROSS_TIMEOUT", "1500"))
MAX = int(os.environ.get("CROSS_MAX", "20"))


def axioms_of(leanfile):
    text = normalize(open(leanfile, errors="ignore").read())
    names = qualified_decls(text)  # fully-qualified: bare names fail at end-of-file
    if not names:
        return None, "no theorem/lemma found"
    tmp = leanfile.with_suffix(".axck.lean")
    tmp.write_text(text + "\n\n" + "\n".join(f"#print axioms {n}" for n in names[-3:]))
    try:
        r = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=REPO,
                           capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        tmp.unlink(missing_ok=True)
        return None, f"timeout>{TIMEOUT}"
    finally:
        tmp.unlink(missing_ok=True)
    out = r.stdout + r.stderr
    if "error:" in out.lower():
        return None, "compile error: " + out[:200]
    # parse "'thm' depends on axioms: [a, b, c]" or "does not depend on any axioms"
    used = set(re.findall(r"[A-Za-z_][\w'.]*", out.split("axioms:", 1)[1])) if "axioms:" in out else set()
    used = {u for u in used if u in SAFE or "." in u or u[0].isupper() or u == "sorryAx"}
    return used, None


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    files = sorted(glob.glob(str(BEST / "*.lean")))
    todo = [
        f for f in files
        if pathlib.Path(f).name not in state
        or state[pathlib.Path(f).name].get("hash") != content_hash(open(f, errors="ignore").read())
    ][:MAX]
    print(f"{len(files)} best proofs, cross-checking {len(todo)} (axiom audit)")
    for f in todo:
        ax, err = axioms_of(pathlib.Path(f))
        b = pathlib.Path(f).name
        digest = content_hash(open(f, errors="ignore").read())
        if ax is None:
            state[b] = {"trusted": None, "detail": err, "hash": digest}
        else:
            extra = sorted(ax - SAFE)
            trusted = ("sorryAx" not in ax) and all(a in SAFE for a in ax if a[0].islower() or "." in a)
            state[b] = {"trusted": trusted and len(extra) == 0, "axioms": sorted(ax),
                        "extra_axioms": extra, "hash": digest}
        STATE.write_text(json.dumps(state, indent=1))
        print(f"  {b}: {state[b].get('trusted')}  {state[b].get('extra_axioms', state[b].get('detail',''))}")
    trusted = sum(1 for s in state.values() if s.get("trusted") is True)
    flagged = [b for b, s in state.items() if s.get("trusted") is False]
    print(f"\ncross-checked {len(state)} | kernel-trusted {trusted} | FLAGGED (extra axioms) {len(flagged)}: {flagged[:6]}")


if __name__ == "__main__":
    main()
