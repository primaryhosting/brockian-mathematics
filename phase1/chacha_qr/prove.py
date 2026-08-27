#!/usr/bin/env python3
"""prove.py — ChaCha20 quarter-round bijectivity, discharged by two independent SMT
engines.

The ChaCha20 quarter-round (RFC 8439) is a full round function over a 128-bit state:
four rounds of modular add + xor + fixed rotate.  We prove it is INJECTIVE (hence,
being an endofunction on a finite set, a bijection): no two distinct states share a
quarter-round image.  This is a genuinely harder QF_BV instance than the SHA-256
diffusion identities — it mixes wrapping addition with rotation and xor.

Two independent SMT engines settle it:
- Z3 4.16.0   (SMT/SAT, bit-blast)
- cvc5 1.3.4  (SMT/SAT, independent codebase)

HONEST SCOPE: this is a TWO-prover (SMT-family) obligation.  A kernel-checked Lean
proof of quarter-round INVERTIBILITY (QRinv ∘ QR = id) is future work — it needs a
rotate-cancel lemma we did not close here — so the Lean leg is marked not-attempted,
not claimed.  Z3 and cvc5 share the SMT-LIB frontend and bit-blasting approach, so
their agreement is a corroboration against an engine-specific bug, not independence
in the strong sense.  Stated, not buried.

Run:  python3 phase1/chacha_qr/prove.py
"""
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OBL_DIR = os.path.join(HERE, "obligations")
OUT = os.path.join(HERE, "certificate.json")

OBLIGATIONS = [
    ("chacha20_qr_injective",
     "ChaCha20 quarter-round (RFC 8439) is INJECTIVE: QR(s1) = QR(s2) => s1 = s2 "
     "over the 128-bit state — hence a bijection. A full add/rotate/xor round function."),
]


def smt_discharge(solver, smt_path):
    try:
        r = subprocess.run([solver, smt_path], capture_output=True, text=True, timeout=180)
    except FileNotFoundError:
        return "unavailable"
    out = (r.stdout + r.stderr).strip().splitlines()
    return "proved" if out and out[-1].strip() == "unsat" else "FAILED"


def canonical_payload(obls, provers):
    return json.dumps({"provers": provers, "obligations": obls}, sort_keys=True, separators=(",", ":"))


def main():
    cvc5_bin = os.path.expanduser("~/.local/bin/cvc5")
    cvc5_cmd = cvc5_bin if os.path.exists(cvc5_bin) else "cvc5"

    obls = []
    for stem, statement in OBLIGATIONS:
        smt_path = os.path.join(OBL_DIR, stem + ".smt2")
        z3v = smt_discharge("z3", smt_path)
        cvc5v = smt_discharge(cvc5_cmd, smt_path)
        obls.append({
            "name": stem, "statement": statement, "smt2": open(smt_path).read(),
            "z3":   {"verdict": z3v,   "solver": "Z3 4.16.0",  "logic": "QF_BV", "method": "bit-blast to SAT; unsat of the negation"},
            "cvc5": {"verdict": cvc5v, "solver": "cvc5 1.3.4", "logic": "QF_BV", "method": "independent SMT engine; unsat of the negation"},
            "lean": {"verdict": "not-attempted", "theorem": None, "checker": "Lean 4 kernel + AXLE",
                     "method": "kernel-checked invertibility (QRinv o QR = id) is future work; SMT-only obligation (stated honestly)"},
            "cross_verified": (z3v == "proved" and cvc5v == "proved"),
            "coverage": "2-prover SMT (Z3, cvc5) — kernel-algebra leg not attempted",
        })

    provers = [
        "Z3 4.16.0 (SMT — bit-blast to SAT)",
        "cvc5 1.3.4 (SMT — independent engine; same SMT-LIB family, so a corroboration not an independence)",
    ]
    payload = canonical_payload(obls, provers)
    digest = hashlib.sha256(payload.encode()).hexdigest()
    all_cv = all(o["cross_verified"] for o in obls)

    cert = {
        "title": "The Verification Foundry — ChaCha20 Quarter-Round Bijectivity Certificate",
        "subject": "A real crypto round function proved injective by two independent SMT engines",
        "provers": provers,
        "obligations": obls,
        "all_cross_verified": all_cv,
        "sha256": digest,
        "note": "Portable evidence: recompute sha256 over {provers, obligations} and re-run any SMT solver "
                "on the embedded smt2 (unsat = injective). No access to our pipeline required. HONEST SCOPE: "
                "TWO-prover SMT obligation; a kernel-checked Lean invertibility proof is future work and is "
                "marked not-attempted, not claimed. Z3 and cvc5 are both SMT/SAT engines — agreement here "
                "guards against an engine-specific bug but is corroboration, not strong independence.",
        "recheck": "python3 phase1/recheck.py phase1/chacha_qr/certificate.json  (or --solver=cvc5)",
    }
    json.dump(cert, open(OUT, "w"), indent=2)

    print(f"{'obligation':<26} {'Z3':<8} {'cvc5':<8} cross-verified")
    print("-" * 56)
    for o in obls:
        print(f"{o['name']:<26} {o['z3']['verdict']:<8} {o['cvc5']['verdict']:<8} "
              f"{'YES' if o['cross_verified'] else '—'}")
    print("-" * 56)
    print(f"sha256: {digest}")
    print(f"certificate -> {os.path.relpath(OUT, ROOT)}")
    return 0 if all_cv else 1


if __name__ == "__main__":
    sys.exit(main())
