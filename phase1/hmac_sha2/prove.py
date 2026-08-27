#!/usr/bin/env python3
"""prove.py — Phase-1 proof-of-life, HMAC-SHA-2 edition.

This is the "scale it to a real HMAC/SHA obligation" step the base Phase-1 README
names as the next joint engineering: instead of generic crypto idioms, the five
obligations here are the decidable bitvector facts that sit INSIDE HMAC-SHA-256 —
the SHA-256 round selectors (Ch, Maj), the HMAC key-padding structure, and the
modular-add associativity of the compression fold.

Honest scope (stated, not buried): this proves the DECIDABLE bitvector obligations
of HMAC-SHA-256, not its full functional correctness or any security property. It
is exactly the impl-vs-spec layer a gate certifies — e.g. that the FIPS 180-4 XOR
form of Ch/Maj equals the OR form a constant-time implementation emits. Each is
discharged by TWO independent provers and bound into one hash-sealed certificate:

- Prover A: Z3 4.16.0 (SMT/SAT) — runs obligations/*.smt2; asserts the negation,
  unsat = proved. A propositional bit-blast search.
- Prover B: Lean 4 kernel + AXLE — proof by DIFFERENT mathematics: per-bit
  reduction (`BitVec.getLsbD`) + Bool case analysis for the bitwise identities, a
  literal constant-fold for the pad constant, and `BitVec.add_assoc` for the fold.
  Re-verified by the AXLE cloud prover and axiom-audited (axioms subset of
  {propext, Classical.choice, Quot.sound}; NO bv_decide SAT axiom, so the Lean leg
  is not a second SAT solver). Verdict read from the module's attestation.

An obligation is CROSS-VERIFIED only when both provers agree. The certificate embeds
the exact SMT-LIB2 and the Lean theorem name and carries a SHA-256 over the payload
so a third party can recompute the hash and re-run any SMT solver — no pipeline of
ours required. See ../recheck.py.

Run:  python3 phase1/hmac_sha2/prove.py
"""
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OBL_DIR = os.path.join(HERE, "obligations")
ATTEST = os.path.join(ROOT, "registry", "attestations", "HighAssuranceHmacSha2.json")
OUT = os.path.join(HERE, "certificate.json")

# (smt file stem, human statement, fully-qualified Lean theorem, Lean closing method)
OBLIGATIONS = [
    ("sha256_ch_spec_eq_impl",
     "SHA-256 Ch: (x & y) ^ (~x & z) = (x & y) | (~x & z)  — the FIPS 180-4 'choice' "
     "selector's spec (XOR) form equals the constant-time (OR) form",
     "Brockian.HighAssurance.HmacSha2.sha256_ch_spec_eq_impl",
     "kernel-checked per-bit reduction (BitVec.getLsbD) + Bool case analysis"),
    ("sha256_maj_spec_eq_impl",
     "SHA-256 Maj: (x&y) ^ (x&z) ^ (y&z) = (x&y) | (x&z) | (y&z)  — the 'majority' "
     "selector's spec (XOR) form equals the OR form",
     "Brockian.HighAssurance.HmacSha2.sha256_maj_spec_eq_impl",
     "kernel-checked per-bit reduction (BitVec.getLsbD) + Bool case analysis"),
    ("hmac_key_pad_difference",
     "HMAC: (k ^ ipad) ^ (k ^ opad) = ipad ^ opad  — the inner/outer padded-key "
     "difference is independent of the key",
     "Brockian.HighAssurance.HmacSha2.hmac_key_pad_difference",
     "kernel-checked per-bit reduction (BitVec.getLsbD) + Bool case analysis"),
    ("hmac_pad_xor_const",
     "HMAC pads: 0x36363636 ^ 0x5c5c5c5c = 0x6a6a6a6a  — ipad ^ opad is the fixed "
     "constant 0x6a per byte, independent of any key",
     "Brockian.HighAssurance.HmacSha2.hmac_pad_xor_const",
     "kernel `decide` over the literal BitVec (constant fold — no SAT axiom)"),
    ("sha256_compress_add_assoc",
     "SHA-256 compression: (a + b) + c = a + (b + c) mod 2^32  — associativity of the "
     "modular add that folds T1 = h + S1(e) + Ch + Kt + Wt",
     "Brockian.HighAssurance.HmacSha2.sha256_compress_add_assoc",
     "kernel-checked BitVec.add_assoc"),
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
        print("NOTE: no Lean attestation yet at registry/attestations/HighAssuranceHmacSha2.json —")
        print("      run scripts/attest.py on Brockian/HighAssuranceHmacSha2.lean first.\n")

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
               "Lean 4 kernel + AXLE (proof by per-bit BitVec reasoning / algebra, axiom-audited — NOT a SAT solver)"]
    payload = canonical_payload(obls, provers)
    digest = hashlib.sha256(payload.encode()).hexdigest()

    all_cv = all(o["cross_verified"] for o in obls)
    cert = {
        "title": "The Verification Foundry — Phase-1 Cross-Verification Certificate (HMAC-SHA-2)",
        "subject": "The decidable bitvector obligations inside HMAC-SHA-256, discharged by two independent provers",
        "provers": provers,
        "obligations": obls,
        "all_cross_verified": all_cv,
        "sha256": digest,
        "note": "Portable evidence: recompute sha256 over {provers, obligations} and re-run any SMT "
                "solver on each embedded smt2 (unsat = proved). No access to our pipeline required. "
                "See ../recheck.py. HONEST SCOPE: these are the small, DECIDABLE QF_BV obligations that "
                "sit inside HMAC-SHA-256 (the Ch/Maj round selectors, the HMAC key-pad structure, the "
                "compression fold's modular-add associativity) — NOT a proof of HMAC-SHA-256 functional "
                "correctness or any security property. The point is the impl-vs-spec + independent-agreement "
                "+ re-checkability discipline on real cryptographic structure, e.g. that the FIPS 180-4 XOR "
                "form of Ch/Maj equals the OR form a constant-time implementation emits. The two provers use "
                "DIFFERENT mathematics: Z3 bit-blasts to SAT; Lean is a kernel-checked per-bit/algebraic proof "
                "re-verified and axiom-audited by AXLE (its axiom gate rejects bv_decide's native SAT/LRAT "
                "axiom, so the Lean leg is not a second SAT solver). Agreement across two different methods is "
                "stronger than agreement across two SAT engines.",
        "recheck": "python3 phase1/recheck.py phase1/hmac_sha2/certificate.json",
    }
    json.dump(cert, open(OUT, "w"), indent=2)

    print(f"{'obligation':<28} {'Z3':<9} {'Lean/AXLE':<10} agree")
    print("-" * 60)
    for o in obls:
        print(f"{o['name']:<28} {o['z3']['verdict']:<9} {o['lean']['verdict']:<10} "
              f"{'YES' if o['cross_verified'] else '—'}")
    print("-" * 60)
    print(f"ALL CROSS-VERIFIED: {all_cv}")
    print(f"sha256: {digest}")
    print(f"certificate -> {os.path.relpath(OUT, ROOT)}")
    return 0 if all_cv else 1


if __name__ == "__main__":
    sys.exit(main())
