#!/usr/bin/env python3
"""smt_gate.py — a Phase-1 multi-prover cross-verification demonstrator.

Proves three security-relevant properties with Z3 (SMT), and cross-checks each
against the SAME statement proved in Lean 4 / Mathlib and independently verified
by AXLE (recorded in registry/theorems.json). A property is CROSS-VERIFIED only
when BOTH legs agree: Z3 proves it (the negation is UNSAT) AND the mirror Lean
theorem is registered PROVED.

This is the answer to "your gate is Lean-only": the same class of obligation is
discharged by an SMT solver — exactly the toolchain seL4's binary translation
validation and Galois's SAW/Cryptol workflow rely on — and the two independent
verdicts are required to agree.

Run:  python3 scripts/smt_gate.py
Emits: docs/galois/smt_cross_verification.json  (+ a printed report)
Stdlib + z3-solver.
"""
import json
import os
import sys

import z3

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REG = os.path.join(REPO, "registry", "theorems.json")
OUT = os.path.join(REPO, "docs", "galois", "smt_cross_verification.json")


def z3_proves(name, build_negation):
    """A property is valid iff its negation is UNSAT. Returns (verdict, detail)."""
    s = z3.Solver()
    s.add(build_negation())
    r = s.check()
    if r == z3.unsat:
        return "PROVED", "negation UNSAT"
    if r == z3.sat:
        return "REFUTED", f"counterexample: {s.model()}"
    return "UNKNOWN", str(r)


# ── Property 1: XOR one-time-pad / stream-cipher involution (bitvector theory) ──
def neg_xor_involution():
    m, k = z3.BitVecs("m k", 8)
    return (m ^ k) ^ k != m


# ── Property 2: access-control default-deny (boolean theory) ──
def neg_default_deny():
    inScope, isPriv, isUnowned = z3.Bools("inScope isPriv isUnowned")
    canAccess = z3.Or(inScope, isPriv, isUnowned)
    # claim: all three grants false  ⇒  no access. Negation: they're false yet access granted.
    return z3.And(z3.Not(inScope), z3.Not(isPriv), z3.Not(isUnowned), canAccess)


# ── Property 3: unauthorized-write memory frame (array + bool theory) ──
def neg_unauth_write_frame():
    mem = z3.Array("mem", z3.IntSort(), z3.IntSort())
    a, v, x = z3.Ints("a v x")
    auth = z3.Bool("auth")
    guarded = z3.If(z3.And(auth, x == a), v, z3.Select(mem, x))
    # claim: auth = false  ⇒  guarded read equals the original memory at every x.
    return z3.And(z3.Not(auth), guarded != z3.Select(mem, x))


PROPERTIES = [
    dict(id="xor_otp_involution",
         english="(m XOR k) XOR k = m — one-time-pad / stream-cipher decryption inverts encryption",
         theory="bitvector",
         neg=neg_xor_involution,
         lean="Brockian.HighAssurance.SMTMirror.xor_otp_involution"),
    dict(id="default_deny",
         english="access is denied when none of {in-scope, privileged, unowned} holds",
         theory="boolean",
         neg=neg_default_deny,
         lean="Brockian.HighAssurance.SMTMirror.default_deny_denies"),
    dict(id="unauth_write_frame",
         english="an unauthorized write leaves every memory address unchanged",
         theory="array",
         neg=neg_unauth_write_frame,
         lean="Brockian.HighAssurance.SMTMirror.unauth_write_frame"),
]


def lean_register(name, ts):
    for t in ts:
        if t["name"] == name:
            return t.get("register", "ABSENT")
    return "ABSENT"


def main():
    ts = json.load(open(REG))
    ts = ts if isinstance(ts, list) else ts.get("theorems", [])
    rows = []
    for p in PROPERTIES:
        z3_verdict, z3_detail = z3_proves(p["id"], p["neg"])
        lean_reg = lean_register(p["lean"], ts)
        agree = (z3_verdict == "PROVED" and lean_reg == "PROVED")
        rows.append(dict(property=p["id"], english=p["english"], theory=p["theory"],
                         z3=z3_verdict, z3_detail=z3_detail,
                         lean_theorem=p["lean"], lean_axle=lean_reg,
                         cross_verified=agree))
    cert = dict(
        title="Multi-prover cross-verification (Z3 SMT × Lean/AXLE)",
        z3_version=z3.get_version_string(),
        lean_env="lean-4.32.2",
        note=("Each property is discharged independently by Z3 (SMT) and by Lean 4/Mathlib "
              "(AXLE-verified). CROSS-VERIFIED requires BOTH verdicts to agree."),
        properties=rows,
        all_cross_verified=all(r["cross_verified"] for r in rows),
    )
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    json.dump(cert, open(OUT, "w"), indent=2)

    print(f"Multi-prover cross-verification  (Z3 {z3.get_version_string()}  ×  Lean/AXLE lean-4.32.2)\n")
    for r in rows:
        mark = "✓ CROSS-VERIFIED" if r["cross_verified"] else "✗ MISMATCH"
        print(f"  [{mark}]  {r['property']}  ({r['theory']})")
        print(f"       Z3: {r['z3']:8}   Lean/AXLE: {r['lean_axle']:10} {r['lean_theorem']}")
    print(f"\n  ALL CROSS-VERIFIED: {cert['all_cross_verified']}")
    print(f"  certificate -> {os.path.relpath(OUT, REPO)}")
    return 0 if cert["all_cross_verified"] else 1


if __name__ == "__main__":
    sys.exit(main())
