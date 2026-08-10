#!/usr/bin/env python3
"""novelty_gate.py — SEMANTIC check that a frontier target has no Mathlib equivalent,
using LeanSearch (semantic search over Mathlib). For each target we query LeanSearch
with its statement and inspect the top results: a target is flagged LIKELY-PRESENT only
if a distinctive concept token from its name actually appears in a returned Mathlib
declaration name/module (high precision — a bare semantic "nearest" match doesn't count).
Otherwise it's treated as NOVEL (worth spending compute on).

Then re-ranks frontier_queue.json: likely-present → rank 9 (deprioritized, not deleted).
Resumable via novelty_report.json; paced. Falls back to NOVEL on any query error.
"""
import json
import os
import pathlib
import re
import time
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
QUEUE = ROOT / "frontier_queue.json"
OUT = ROOT / "novelty_report.json"
ENDPOINT = "https://leansearch.net/search"
COMMON = {"theorem", "statement", "problem", "conjecture", "exists", "terminates",
          "sign", "invariant", "phase", "bound", "inequality", "regularity",
          "correlation", "singularity", "reciprocity", "equilibrium", "impossibility",
          "generation", "independent", "finite", "three", "second", "implies", "prime", "primes",
          "color", "gaussian", "partition", "regulator", "penrose", "willmore"}
PACE = float(os.environ.get("NOVELTY_PACE", "2.5"))   # LeanSearch 403s if hammered
MAX = int(os.environ.get("NOVELTY_MAX", "120"))


def tokens(name):
    parts = re.split(r"[._]", name.replace("Frontier.", ""))
    return [p for p in parts if len(p) >= 5 and p.lower() not in COMMON]


def leansearch(query, k=6):
    data = json.dumps({"query": [query[:300]], "num_results": k}).encode()
    hdrs = {"Content-Type": "application/json",
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36"}
    for attempt in range(4):
        req = urllib.request.Request(ENDPOINT, data=data, headers=hdrs)
        try:
            with urllib.request.urlopen(req, timeout=25) as r:
                return json.loads(r.read().decode())
        except urllib.error.HTTPError as e:
            if e.code in (403, 429) and attempt < 3:
                time.sleep(5 * (attempt + 1))   # back off on rate-limit
                continue
            raise


def main():
    q = json.loads(QUEUE.read_text())["queue"]
    report = json.loads(OUT.read_text()) if OUT.exists() else {}
    todo = [it for it in q if it["target"] not in report][:MAX]
    print(f"{len(q)} frontier targets; LeanSearch novelty-checking {len(todo)}")
    for it in todo:
        toks = [t.lower() for t in tokens(it["target"])]
        present, matched = False, None
        try:
            res = leansearch(it.get("statement", it["target"]))
        except Exception as e:  # noqa: BLE001
            print(f"  skip (retry next run) {it['target']}: {str(e)[:60]}")
            time.sleep(PACE)
            continue   # do NOT record — leave for retry
        rows = res[0] if res and isinstance(res, list) else []
        for row in rows[:6]:
            r = row.get("result", row)
            blob = (" ".join(r.get("name", [])) + " " + " ".join(r.get("module", []))).lower()
            # high precision: require ALL distinctive tokens to co-occur (avoids eponym
            # false positives like 'borel' matching Borel σ-algebras vs Borel determinacy)
            if toks and all(t in blob for t in toks):
                present, matched = True, {"decl": ".".join(r.get("name", [])), "on": toks}
                break
        report[it["target"]] = {"difficulty": it["difficulty"], "likely_present": present,
                                "match": matched}
        OUT.write_text(json.dumps(report, indent=1))
        time.sleep(PACE)

    present = [t for t, r in report.items() if r.get("likely_present")]
    # re-rank: deprioritize likely-present in the queue
    changed = 0
    for it in q:
        if report.get(it["target"], {}).get("likely_present") and it.get("rank", 5) < 9:
            it["rank"] = 9
            changed += 1
    QUEUE.write_text(json.dumps({"count": len(q), "queue": q}, indent=1))
    print(f"checked {len(report)}/{len(q)} | likely-in-Mathlib: {len(present)} | "
          f"NOVEL: {len(report)-len(present)} | deprioritized {changed}")
    for t in present[:20]:
        print(f"  present: {t}  <- {report[t]['match']}")


if __name__ == "__main__":
    main()
