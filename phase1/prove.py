#!/usr/bin/env python3
"""prove.py — the Phase-1 proof-of-life: discharge real crypto-implementation
obligations by TWO independent provers and emit one hash-sealed, re-checkable certificate
(SHA-256 content digest — tamper-evident, not a keyed signature).

- Prover A: Z3 (SMT/SAT) — runs the SMT-LIB2 query in obligations/*.smt2; unsat = proved.
  Z3 discharges by bit-blasting to SAT: a genuine propositional search.
- Prover B: Lean 4 kernel + AXLE — a proof by *different mathematics*: for the three
  non-trivial obligations, kernel-checked BitVec algebra (Mathlib rewrite lemmas); for the two
  constant-mask selects, bv_decide preprocessing that constant-folds to rfl. The whole module
  is re-verified by the AXLE cloud prover and axiom-audited (axioms ⊆ {propext, Classical.choice,
  Quot.sound}). Verdict + axiom set read from registry/attestations/CryptoIdioms.json.

  HONEST NOTE (surfaced by the prover, kept here): AXLE's axiom gate REJECTS bv_decide's
  native SAT/LRAT axiom as outside the allowed standard set — so the Lean leg is NOT "a second
  SAT solver," it is a kernel-checked proof by algebra. That makes the two provers *more*
  independent (SAT search vs. algebraic reasoning), not less, and the agreement stronger.

An obligation is CROSS-VERIFIED only when both provers agree. The certificate embeds the exact
SMT-LIB2 and the Lean theorem name, and carries a SHA-256 over the mathematical payload so a
third party can (a) recompute the hash and (b) re-run any SMT solver on the embedded query —
without our pipeline. See recheck.py.

Run:  python3 phase1/prove.py
"""
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OBL_DIR = os.path.join(ROOT, "phase1", "obligations")
ATTEST = os.path.join(ROOT, "registry", "attestations", "HighAssuranceCryptoIdioms.json")
OUT = os.path.join(ROOT, "phase1", "certificate.json")

# (smt file stem, human statement, fully-qualified Lean theorem, Lean closing method)
OBLIGATIONS = [
    ("otp_involution", "(m ^ k) ^ k = m  — one-time-pad / stream-cipher decryption inverts encryption",
     "Brockian.HighAssurance.CryptoIdioms.otp_involution",
     "kernel-checked BitVec algebra (xor_assoc, xor_self, xor_zero)"),
    ("mask_select_identity", "(mask & a) | (~mask & a) = a  — the masking identity behind constant-time select",
     "Brockian.HighAssurance.CryptoIdioms.mask_select_identity",
     "kernel-checked BitVec algebra (and_or_distrib_right, or_not_self, allOnes_and)"),
    ("ct_select_true", "ctSelect(all-ones, a, b) = a  — constant-time conditional selects a",
     "Brockian.HighAssurance.CryptoIdioms.ct_select_true",
     "bv_decide preprocessing constant-folds the literal mask to rfl"),
    ("ct_select_false", "ctSelect(0, a, b) = b  — constant-time conditional selects b",
     "Brockian.HighAssurance.CryptoIdioms.ct_select_false",
     "bv_decide preprocessing constant-folds the literal mask to rfl"),
    ("xor_swap", "the XOR-swap trick returns (b, a)  — in-place swap with no temporary",
     "Brockian.HighAssurance.CryptoIdioms.xor_swap",
     "kernel-checked BitVec algebra after Prod.mk.injEq split"),
]


def z3_discharge(smt_path):
    r = subprocess.run(["z3", smt_path], capture_output=True, text=True, timeout=120)
    out = (r.stdout + r.stderr).strip()
    # unsat of the negation == the property is proved
    return ("proved" if out.splitlines() and out.splitlines()[-1].strip() == "unsat" else "FAILED"), out


def lean_verdicts():
    """Map fully-qualified name -> 'proved'/'FAILED' from the AXLE attestation."""
    if not os.path.exists(ATTEST):
        return {}
    d = json.load(open(ATTEST))
    m = {}
    for decl in d.get("declarations", []):
        ok = decl.get("axle_verdict") == "verified" and decl.get("axioms_ok") is True
        m[decl["name"]] = "proved" if ok else "FAILED"
    return m


def canonical_payload(obls, provers):
    """The math content that the hash covers (NOT the timestamp)."""
    return json.dumps({"provers": provers, "obligations": obls}, sort_keys=True, separators=(",", ":"))


def main():
    lean = lean_verdicts()
    if not lean:
        print("NOTE: no Lean attestation yet at registry/attestations/CryptoIdioms.json —")
        print("      run attest on Brockian/HighAssuranceCryptoIdioms.lean first for a full certificate.\n")

    obls = []
    for stem, statement, thm, method in OBLIGATIONS:
        smt_path = os.path.join(OBL_DIR, stem + ".smt2")
        z3v, _ = z3_discharge(smt_path)
        smt2 = open(smt_path).read()
        lv = lean.get(thm, "pending")
        agree = (z3v == "proved" and lv == "proved")
        obls.append({
            "name": stem, "statement": statement, "smt2": smt2,
            "z3": {"verdict": z3v, "solver": "Z3 4.16.0", "logic": "QF_BV", "method": "bit-blast to SAT; unsat of the negation"},
            "lean": {"verdict": lv, "theorem": thm,
                     "checker": "Lean 4 kernel + AXLE re-verification (lean-4.32.2), axiom-clean",
                     "method": method},
            "cross_verified": agree,
        })

    provers = ["Z3 4.16.0 (SMT — bit-blast to SAT)",
               "Lean 4 kernel + AXLE (proof by BitVec algebra / constant-fold, axiom-audited — NOT a SAT solver)"]
    payload = canonical_payload(obls, provers)
    digest = hashlib.sha256(payload.encode()).hexdigest()

    all_cv = all(o["cross_verified"] for o in obls)
    cert = {
        "title": "The Verification Foundry — Phase-1 Cross-Verification Certificate",
        "subject": "Real crypto-implementation obligations, discharged by two independent provers",
        "provers": provers,
        "obligations": obls,
        "all_cross_verified": all_cv,
        "sha256": digest,
        "note": "Portable evidence: recompute sha256 over {provers, obligations} and re-run any SMT "
                "solver on each embedded smt2 (unsat = proved). No access to our pipeline required. "
                "See recheck.py. HONEST SCOPE: these are small, decidable QF_BV obligations — the point "
                "is the independent-agreement + re-checkability discipline, not proof depth. The two "
                "provers use DIFFERENT mathematics: Z3 bit-blasts to SAT; Lean is a kernel-checked "
                "algebraic proof re-verified and axiom-audited by AXLE (its axiom gate rejects "
                "bv_decide's native SAT/LRAT axiom, so the Lean leg is not a second SAT solver). "
                "Agreement across two different methods is stronger than agreement across two SAT engines.",
        "recheck": "python3 phase1/recheck.py phase1/certificate.json",
    }
    json.dump(cert, open(OUT, "w"), indent=2)

    print(f"{'obligation':<24} {'Z3':<9} {'Lean/AXLE':<10} agree")
    print("-" * 56)
    for o in obls:
        print(f"{o['name']:<24} {o['z3']['verdict']:<9} {o['lean']['verdict']:<10} "
              f"{'YES' if o['cross_verified'] else '—'}")
    print("-" * 56)
    print(f"ALL CROSS-VERIFIED: {all_cv}")
    print(f"sha256: {digest}")
    print(f"certificate -> {os.path.relpath(OUT, ROOT)}")
    return 0 if all_cv else 1


if __name__ == "__main__":
    sys.exit(main())
