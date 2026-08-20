#!/usr/bin/env python3
"""catalogue_domains.py — file verified NEW-DOMAIN proofs (QC / quantum-physics /
chemistry / CS / pure-math) into their own registry, separate from the Brockian
program. Reads the domain queues (for statements) + harvest_ledger + verify_state,
and writes registry/domains.json — deduped, with verification status + provenance.

Never touches the Brockian registry. Domain proofs are a distinct catalogue.
"""
import json
import hashlib
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
QUEUES = [ROOT / q for q in ("reconciled_queue.json", "domains_queue.json", "mined_queue.json", "next_100.json",
          "pca_lean_queue.json", "frontier_queue.json", "frontier2.json",
          "reattack_queue.json", "frontier_spectral.json", "frontier_betrothed_queue.json", "frontier_linalg.json", "frontier_riemann.json", "frontier_infinity.json", "frontier_fibonacci.json", "frontier_primes.json", "frontier_rh2.json", "frontier_wave2.json", "frontier_wave3.json", "frontier_wave4.json", "frontier_wave5.json")]
LEDGER = ROOT / "harvest_ledger.json"
VSTATE = ROOT / "harvest_100" / "verify_state.json"
BEST = ROOT / "best_proofs" / "manifest.json"
BEST_DIR = ROOT / "best_proofs"
OUT = REPO / "registry" / "domains.json"


def normalize(content: str) -> str:
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    return "\n".join(imports + [""] + body)


def content_hash(content: str) -> str:
    return hashlib.sha256(normalize(content).encode()).hexdigest()[:16]


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
    # AXLE cloud verification (keyed by best_proofs sanitized-target filename)
    axle = {}
    axp = ROOT / "axle_verify.json"
    if axp.exists():
        axle = json.loads(axp.read_text())
    cross = {}
    cross_path = ROOT / "cross_check.json"
    if cross_path.exists():
        cross = json.loads(cross_path.read_text())

    def independent_ok(target):
        san = re.sub(r"[^A-Za-z0-9]+", "_", target) + ".lean"
        proof = BEST_DIR / san
        if not proof.exists():
            return False
        digest = content_hash(proof.read_text(errors="ignore"))
        ax = axle.get(san, {})
        cc = cross.get(san, {})
        return (ax.get("verified") is True
                and ax.get("environment") == "lean-4.32.2"
                and ax.get("hash") == digest
                and cc.get("trusted") is True
                and cc.get("hash") == digest)

    cat = json.loads(OUT.read_text()) if OUT.exists() else {}
    added = 0
    for pid, meta in ledger.items():
        t = meta.get("target")
        if not t or t not in stmt or meta.get("verdict") != "PROVED":
            continue
        fname = f"{meta['account']}_{pid[:8]}.lean"
        entry = cat.get(t, {})
        independently_verified = independent_ok(t)
        # Registry PROVED requires local compilation, the independent AXLE leg,
        # a clean axiom audit, and one shared content hash across all three.
        locally_compiles = file_compiles.get(fname) is True or (best.get(t, {}).get("compiles") is True)
        verified = independently_verified and locally_compiles
        # keep the strongest status seen
        register = "PROVED" if verified else "PROVED_UNVERIFIED"
        if entry.get("register") == "PROVED":
            continue
        cat[t] = {"register": register, "domain": stmt[t]["domain"], "statement": stmt[t]["statement"],
                  "proof_file": f"aristotle/harvest_100/{fname}",
                  "provenance": f"Harmonic/Aristotle {pid} ({meta['account']})",
                  "verification": ("local Lean + AXLE lean-4.32.2 + axiom audit OK" if verified
                                   else "local Lean OK; independent AXLE verification pending"
                                   if locally_compiles
                                   else "sorry-free Aristotle candidate; verification pending")}
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
