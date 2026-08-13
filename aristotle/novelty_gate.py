#!/usr/bin/env python3
"""novelty_gate.py — scoped Mathlib declaration-name overlap check.

LeanSearch is queried with each target statement. A target is marked ``likely_present``
only when all distinctive target-name tokens occur in a returned Mathlib declaration
name/module. A negative result means only "no distinctive Mathlib name match found."
It does NOT establish mathematical novelty, first-formalization novelty, or absence from
other Lean repositories or the literature.

Likely Mathlib-name matches are deprioritized to rank 9, not deleted. Results are cached
in novelty_report.json and requests are paced.
"""
import json
import os
import pathlib
import re
import time
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
QUEUE = ROOT / __import__("os").environ.get("NOVELTY_QUEUE", "frontier_queue.json")
OUT = ROOT / __import__("os").environ.get("NOVELTY_OUT", "novelty_report.json")
ENDPOINT = "https://leansearch.net/search"
COMMON = {"theorem", "statement", "problem", "conjecture", "exists", "terminates",
          "sign", "invariant", "phase", "bound", "inequality", "regularity",
          "correlation", "singularity", "reciprocity", "equilibrium", "impossibility",
          "generation", "independent", "finite", "three", "second", "implies", "prime", "primes",
          "color", "gaussian", "partition", "regulator", "penrose", "willmore"}
PACE = float(os.environ.get("NOVELTY_PACE", "2.5"))   # LeanSearch 403s if hammered
MAX = int(os.environ.get("NOVELTY_MAX", "120"))
SCOPE = ("distinctive Mathlib declaration-name match only; "
         "not mathematical or formalization novelty")


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
    print(f"{len(q)} frontier targets; Mathlib-name overlap-checking {len(todo)}")
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
                                "match": matched, "scope": SCOPE,
                                "interpretation": ("distinctive Mathlib name match found"
                                                   if present else
                                                   "no distinctive Mathlib name match found")}
        OUT.write_text(json.dumps(report, indent=1))
        time.sleep(PACE)

    # Backfill cached records written by older versions with claim-safe semantics.
    for r in report.values():
        r.setdefault("scope", SCOPE)
        r.setdefault("interpretation", ("distinctive Mathlib name match found"
                                        if r.get("likely_present") else
                                        "no distinctive Mathlib name match found"))
    OUT.write_text(json.dumps(report, indent=1))

    present = [t for t, r in report.items() if r.get("likely_present")]
    # re-rank: deprioritize likely-present in the queue
    changed = 0
    for it in q:
        if report.get(it["target"], {}).get("likely_present") and it.get("rank", 5) < 9:
            it["rank"] = 9
            changed += 1
    QUEUE.write_text(json.dumps({"count": len(q), "queue": q}, indent=1))
    print(f"checked {len(report)}/{len(q)} | likely-in-Mathlib: {len(present)} | "
          f"no-distinctive-Mathlib-match: {len(report)-len(present)} | "
          f"deprioritized {changed}")
    for t in present[:20]:
        print(f"  present: {t}  <- {report[t]['match']}")


if __name__ == "__main__":
    main()
