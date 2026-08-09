#!/usr/bin/env python3
"""select_best.py — dedup the racing attempts: for each target with ≥1 harvested
PROVED proof (across both accounts + repeats), pick the BEST one and collect it.

Best = compiles (per verify_state, if known) > axiom-clean > shortest. Writes
best_proofs/<sanitized_target>.lean + best_proofs/manifest.json.
"""
import glob
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
H = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
VSTATE = H / "verify_state.json"
OUT = ROOT / "best_proofs"
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    vstate = json.loads(VSTATE.read_text()) if VSTATE.exists() else {}
    compiles = {b: s.get("compiles") for b, s in vstate.items()}

    # gather candidate proofs per target
    by_target = {}
    for pid, meta in ledger.items():
        if meta.get("verdict") != "PROVED":
            continue
        f = H / f"{meta['account']}_{pid[:8]}.lean"
        if not f.exists():
            continue
        text = f.read_text(errors="ignore")
        body = "\n".join(l for l in text.splitlines() if not l.strip().startswith("--"))
        cand = {"file": f, "account": meta["account"], "project_id": pid,
                "lines": len(text.splitlines()), "axiom_clean": not BAD.search(body),
                "compiles": compiles.get(f.name)}
        by_target.setdefault(meta["target"], []).append(cand)

    def score(c):
        # prefer known-compiles, then axiom-clean, then fewer lines
        return (0 if c["compiles"] is True else (1 if c["compiles"] is None else 2),
                0 if c["axiom_clean"] else 1, c["lines"])

    manifest = {}
    for target, cands in by_target.items():
        best = min(cands, key=score)
        safe = re.sub(r"[^A-Za-z0-9]+", "_", target)
        (OUT / f"{safe}.lean").write_text(best["file"].read_text(errors="ignore"))
        manifest[target] = {"chosen": best["file"].name, "account": best["account"],
                            "project_id": best["project_id"], "lines": best["lines"],
                            "axiom_clean": best["axiom_clean"], "compiles": best["compiles"],
                            "n_candidates": len(cands)}
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=1))
    print(f"selected best proof for {len(manifest)} targets "
          f"(from {sum(len(v) for v in by_target.values())} candidates)")


if __name__ == "__main__":
    main()
