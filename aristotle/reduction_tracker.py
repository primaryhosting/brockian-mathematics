#!/usr/bin/env python3
"""reduction_tracker.py — the 40 famous-open conjectures rarely close outright, but
Aristotle often proves a CONDITIONAL REDUCTION ("Conjecture follows from H"). This
detects and tracks those Lean-checked reductions as real partial progress, instead of
scoring the attempt a plain failure.

Heuristic (no build): in harvested B-tier / conjecture files, find declarations that
(a) mention the conjecture's key term and (b) take a hypothesis and conclude it —
i.e. `theorem foo (h : H) : Conjecture` or names like `Conjecture_of_H`. Records
reductions.json for progress tracking.
"""
import glob
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
H = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
OUT = ROOT / "reductions.json"
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
# a declaration with at least one hypothesis binder and a conclusion
DECL = re.compile(r"(?:theorem|lemma)\s+([A-Za-z_][\w']*)\s*(.*?):\s*(.+?):=", re.S)


def main():
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    by_file = {f"{m['account']}_{pid[:8]}.lean": m for pid, m in ledger.items()}
    reductions = {}
    for f in glob.glob(str(H / "*.lean")):
        name = pathlib.Path(f).name
        meta = by_file.get(name, {})
        tier = (meta.get("tier") or "")
        if "B-conjecture" not in tier and "CONJECTURE" not in tier.upper():
            continue
        target = meta.get("target", name)
        key = target.split(".")[-1].replace("Conjecture", "").replace("Problem", "").lower()
        text = open(f, errors="ignore").read()
        for m in DECL.finditer(text):
            nm, binders, concl = m.group(1), m.group(2), m.group(3)
            block_ok = not BAD.search(m.group(0))
            has_hyp = ("(" in binders and ":" in binders) or "→" in concl or "->" in concl
            names_conj = key and (key[:6] in nm.lower() or "_of_" in nm.lower())
            if block_ok and has_hyp and names_conj:
                reductions.setdefault(target, []).append(
                    {"lemma": nm, "hypothesis": binders.strip()[:120] or concl[:120],
                     "source": name, "account": meta.get("account")})
    OUT.write_text(json.dumps(reductions, indent=1))
    n = sum(len(v) for v in reductions.values())
    print(f"tracked {n} candidate conditional reductions across {len(reductions)} conjectures")
    for t, rs in list(reductions.items())[:8]:
        print(f"  {t}: {[r['lemma'] for r in rs]}")


if __name__ == "__main__":
    main()
