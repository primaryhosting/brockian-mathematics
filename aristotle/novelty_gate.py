#!/usr/bin/env python3
"""novelty_gate.py — check frontier targets against the local Mathlib source so we
only spend compute on things with NO Mathlib equivalent. Tokenizes each target name,
greps the Mathlib .lean source once, and flags targets whose distinctive tokens
already appear (likely already formalized) vs. likely-novel.

Heuristic (name-token grep), not a proof of absence — it's a cheap prioritization
filter. Writes novelty_report.json.
"""
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
QUEUE = ROOT / "frontier_queue.json"
OUT = ROOT / "novelty_report.json"
COMMON = {"theorem", "statement", "problem", "conjecture", "exists", "terminates",
          "sign", "toy", "invariant", "phase", "law", "bound", "inequality", "regularity",
          "correlation", "singularity", "reciprocity", "equilibrium", "impossibility"}


def mathlib_src():
    for c in [REPO / ".lake/packages/mathlib/Mathlib",
              pathlib.Path.home() / ".cache/mathlib"]:
        if c.exists():
            return c
    return None


def tokens(name):
    parts = re.split(r"[._]", name.replace("Frontier.", ""))
    return sorted({p for p in parts if len(p) >= 5 and p.lower() not in COMMON})


def main():
    q = json.loads(QUEUE.read_text())["queue"]
    src = mathlib_src()
    all_tokens = sorted({tok for it in q for tok in tokens(it["target"])})
    present = set()
    if src and all_tokens:
        pat = "|".join(re.escape(t) for t in all_tokens)
        try:
            r = subprocess.run(["grep", "-riohwE", pat, str(src), "--include=*.lean"],
                               capture_output=True, text=True, timeout=300)
            present = {w.lower() for w in r.stdout.split()}
        except Exception:  # noqa: BLE001
            pass
    report = {}
    novel = 0
    for it in q:
        toks = tokens(it["target"])
        hits = [t for t in toks if t.lower() in present]
        is_novel = not hits
        novel += is_novel
        report[it["target"]] = {"tier": it["tier"], "difficulty": it["difficulty"],
                                "likely_novel": is_novel, "mathlib_token_hits": hits}
    OUT.write_text(json.dumps(report, indent=1))
    print(f"mathlib source: {'found' if src else 'NOT found (all treated novel)'}")
    print(f"{novel}/{len(q)} targets likely NOVEL (no Mathlib token match)")
    flagged = [t for t, r in report.items() if not r["likely_novel"]]
    print(f"{len(flagged)} likely-already-in-Mathlib (deprioritize):")
    for t in flagged[:20]:
        print(f"  {t}  <- hits {report[t]['mathlib_token_hits']}")


if __name__ == "__main__":
    main()
