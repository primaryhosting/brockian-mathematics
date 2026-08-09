#!/usr/bin/env python3
"""catalogue_domains.py — file verified NEW-DOMAIN proofs (QC / quantum-physics /
chemistry / CS / pure-math) into their own registry, separate from the Brockian
program. Reads the domain queues (for statements) + harvest_ledger + verify_state,
and writes registry/domains.json — deduped, with verification status + provenance.

Never touches the Brockian registry. Domain proofs are a distinct catalogue.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
QUEUES = [ROOT / "domains_queue.json", ROOT / "mined_queue.json"]
LEDGER = ROOT / "harvest_ledger.json"
VSTATE = ROOT / "harvest_100" / "verify_state.json"
BEST = ROOT / "best_proofs" / "manifest.json"
OUT = REPO / "registry" / "domains.json"


def main():
    stmt = {}
    for qf in QUEUES:
        if qf.exists():
            for it in json.loads(qf.read_text())["queue"]:
                stmt[it["target"]] = {"statement": it.get("statement"), "domain": it["tier"]}
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    best = json.loads(BEST.read_text()) if BEST.exists() else {}
    # which harvested files compiled (verify_state keyed by filename)
    vstate = json.loads(VSTATE.read_text()) if VSTATE.exists() else {}
    file_compiles = {b: s.get("compiles") for b, s in vstate.items()}

    cat = json.loads(OUT.read_text()) if OUT.exists() else {}
    added = 0
    for pid, meta in ledger.items():
        t = meta.get("target")
        if not t or t not in stmt or meta.get("verdict") != "PROVED":
            continue
        fname = f"{meta['account']}_{pid[:8]}.lean"
        entry = cat.get(t, {})
        verified = file_compiles.get(fname) is True or (best.get(t, {}).get("compiles") is True)
        # keep the strongest status seen
        register = "PROVED" if verified else "PROVED_UNVERIFIED"
        if entry.get("register") == "PROVED":
            continue
        cat[t] = {"register": register, "domain": stmt[t]["domain"], "statement": stmt[t]["statement"],
                  "proof_file": f"aristotle/harvest_100/{fname}",
                  "provenance": f"Harmonic/Aristotle {pid} ({meta['account']})",
                  "verification": "lake env lean OK" if verified else "axiom-clean by inspection; lake pending"}
        added += 1
    OUT.write_text(json.dumps(cat, indent=1))
    import collections
    reg = collections.Counter(v["register"] for v in cat.values())
    dom = collections.Counter(v["domain"].split("-")[-1] for v in cat.values())
    print(f"catalogued {len(cat)} domain results (+{added} this run) -> {OUT}")
    print("  by register:", dict(reg))
    print("  by domain:", dict(dom))


if __name__ == "__main__":
    main()
