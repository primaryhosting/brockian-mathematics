#!/usr/bin/env python3
"""prove.py — heterogeneous-agreement gate at scale: THREE independent provers on
non-trivial SHA-256 diffusion obligations.

This is the "heterogeneous agreement at scale" step: the base Phase-1 uses two
provers on toy QF_BV idioms; here we add a genuine third independent solver (cvc5)
and scale to real SHA-256 message-schedule structure — the GF(2)-linearity of the
four Sigma/sigma functions, plus the injectivity (bijectivity) of the two small
sigmas.

Three cores, honestly scoped per obligation:
- Z3 4.16.0     (SMT/SAT, bit-blast)            — runs obligations/*.smt2, unsat = proved
- cvc5 1.3.x    (SMT/SAT, independent codebase) — same queries, independent engine
- Lean 4 + AXLE (kernel-checked algebra)        — per-bit / rewrite proof, axiom-audited

HONEST NOTE (the discipline is the pitch): Z3 and cvc5 are both SMT/SAT engines —
they share the SMT-LIB frontend and bit-blasting approach, so their agreement guards
against an engine-specific bug but is NOT independence. Lean/AXLE is the genuinely
different method (kernel algebra, no SAT axiom). The LINEARITY obligations are proved
by all three; the INJECTIVITY obligations are a harder SAT instance the two SMT
engines settle but for which we do not (yet) have a kernel-algebra proof — so their
Lean leg is honestly marked `not-attempted`, and cross-verification for them means
"both independent SMT engines agree." We do not claim a kernel proof we do not have.

Run:  python3 phase1/sha256_diffusion/prove.py
"""
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OBL_DIR = os.path.join(HERE, "obligations")
ATTEST = os.path.join(ROOT, "registry", "attestations", "HighAssuranceSha256Diffusion.json")
OUT = os.path.join(HERE, "certificate.json")

# (smt stem, human statement, Lean theorem or None, Lean method or None)
LEAN_NS = "Brockian.HighAssurance.Sha256Diffusion"
OBLIGATIONS = [
    ("bigsigma0_linear",
     "SHA-256 Sigma0 is GF(2)-linear: Sigma0(x ^ y) = Sigma0(x) ^ Sigma0(y), "
     "Sigma0(v) = ROTR^2 v ^ ROTR^13 v ^ ROTR^22 v",
     f"{LEAN_NS}.Sigma0_linear",
     "kernel-checked: rotate_right distributes over xor (per-bit getLsbD), then AC"),
    ("bigsigma1_linear",
     "SHA-256 Sigma1 is GF(2)-linear: Sigma1(x ^ y) = Sigma1(x) ^ Sigma1(y), "
     "Sigma1(v) = ROTR^6 v ^ ROTR^11 v ^ ROTR^25 v",
     f"{LEAN_NS}.Sigma1_linear",
     "kernel-checked: rotate_right distributes over xor (per-bit getLsbD), then AC"),
    ("smallsigma0_linear",
     "SHA-256 sigma0 is GF(2)-linear: sigma0(x ^ y) = sigma0(x) ^ sigma0(y), "
     "sigma0(v) = ROTR^7 v ^ ROTR^18 v ^ SHR^3 v",
     f"{LEAN_NS}.sigma0_linear",
     "kernel-checked: rotate_right and ushiftRight distribute over xor, then AC"),
    ("smallsigma1_linear",
     "SHA-256 sigma1 is GF(2)-linear: sigma1(x ^ y) = sigma1(x) ^ sigma1(y), "
     "sigma1(v) = ROTR^17 v ^ ROTR^19 v ^ SHR^10 v",
     f"{LEAN_NS}.sigma1_linear",
     "kernel-checked: rotate_right and ushiftRight distribute over xor, then AC"),
    ("smallsigma0_injective",
     "SHA-256 sigma0 is INJECTIVE (a bijection): sigma0(x) = sigma0(y) => x = y "
     "— the message-schedule word is recoverable",
     None, None),
    ("smallsigma1_injective",
     "SHA-256 sigma1 is INJECTIVE (a bijection): sigma1(x) = sigma1(y) => x = y",
     None, None),
]


def smt_discharge(solver, smt_path):
    try:
        r = subprocess.run([solver, smt_path], capture_output=True, text=True, timeout=120)
    except FileNotFoundError:
        return "unavailable"
    out = (r.stdout + r.stderr).strip().splitlines()
    return "proved" if out and out[-1].strip() == "unsat" else "FAILED"


def lean_verdicts():
    if not os.path.exists(ATTEST):
        return {}
    d = json.load(open(ATTEST))
    m = {}
    for decl in d.get("declarations", []):
        ok = decl.get("axle_verdict") == "verified" and decl.get("axioms_ok") is True
        m[decl["name"]] = "proved" if ok else "FAILED"
    return m


def canonical_payload(obls, provers):
    return json.dumps({"provers": provers, "obligations": obls}, sort_keys=True, separators=(",", ":"))


def main():
    lean = lean_verdicts()
    cvc5_bin = os.path.expanduser("~/.local/bin/cvc5")
    cvc5_cmd = cvc5_bin if os.path.exists(cvc5_bin) else "cvc5"

    obls = []
    for stem, statement, thm, method in OBLIGATIONS:
        smt_path = os.path.join(OBL_DIR, stem + ".smt2")
        z3v = smt_discharge("z3", smt_path)
        cvc5v = smt_discharge(cvc5_cmd, smt_path)
        smt2 = open(smt_path).read()
        entry = {
            "name": stem, "statement": statement, "smt2": smt2,
            "z3":   {"verdict": z3v,   "solver": "Z3 4.16.0",  "logic": "QF_BV", "method": "bit-blast to SAT; unsat of the negation"},
            "cvc5": {"verdict": cvc5v, "solver": "cvc5 1.3.4", "logic": "QF_BV", "method": "independent SMT engine; unsat of the negation"},
        }
        if thm is not None:
            lv = lean.get(thm, "pending")
            entry["lean"] = {"verdict": lv, "theorem": thm,
                             "checker": "Lean 4 kernel + AXLE re-verification (lean-4.32.2), axiom-clean",
                             "method": method}
            entry["cross_verified"] = (z3v == "proved" and cvc5v == "proved" and lv == "proved")
            entry["coverage"] = "3-prover (Z3, cvc5, Lean/AXLE)"
        else:
            entry["lean"] = {"verdict": "not-attempted",
                             "theorem": None,
                             "checker": "Lean 4 kernel + AXLE",
                             "method": "no kernel-algebra proof of injectivity attempted; SMT-only obligation (stated honestly)"}
            entry["cross_verified"] = (z3v == "proved" and cvc5v == "proved")
            entry["coverage"] = "2-prover SMT (Z3, cvc5) — kernel-algebra leg not attempted"
        obls.append(entry)

    provers = [
        "Z3 4.16.0 (SMT — bit-blast to SAT)",
        "cvc5 1.3.4 (SMT — independent engine; same SMT-LIB family as Z3, so a corroboration not an independence)",
        "Lean 4 kernel + AXLE (kernel-checked algebra / per-bit reasoning, axiom-audited — the genuinely different method)",
    ]
    payload = canonical_payload(obls, provers)
    digest = hashlib.sha256(payload.encode()).hexdigest()
    all_cv = all(o["cross_verified"] for o in obls)

    cert = {
        "title": "The Verification Foundry — Heterogeneous-Agreement Certificate (SHA-256 diffusion, 3-prover)",
        "subject": "Non-trivial SHA-256 message-schedule obligations under three independent provers",
        "provers": provers,
        "obligations": obls,
        "all_cross_verified": all_cv,
        "sha256": digest,
        "note": "Portable evidence: recompute sha256 over {provers, obligations} and re-run any SMT solver on "
                "each embedded smt2 (unsat = proved). No access to our pipeline required. HONEST SCOPE + "
                "INDEPENDENCE: the four LINEARITY obligations are proved by all three cores; the two "
                "INJECTIVITY obligations are a harder SAT instance settled by the two SMT engines (Z3, cvc5) "
                "with NO kernel-algebra proof attempted — marked not-attempted, not claimed. Z3 and cvc5 are "
                "both SMT/SAT engines (shared SMT-LIB frontend + bit-blasting): their agreement guards against "
                "an engine-specific bug but is a corroboration, not independence. Lean/AXLE is the genuinely "
                "different method (kernel algebra, no SAT axiom). This certificate answers our own objection "
                "'agreement is not independence' by SHOWING the distinction per obligation rather than hiding it.",
        "recheck": "python3 phase1/recheck.py phase1/sha256_diffusion/certificate.json  (or --solver=cvc5 for the 2nd SMT engine)",
    }
    json.dump(cert, open(OUT, "w"), indent=2)

    print(f"{'obligation':<26} {'Z3':<8} {'cvc5':<8} {'Lean/AXLE':<14} agree")
    print("-" * 68)
    for o in obls:
        print(f"{o['name']:<26} {o['z3']['verdict']:<8} {o['cvc5']['verdict']:<8} "
              f"{o['lean']['verdict']:<14} {'YES' if o['cross_verified'] else '—'}")
    print("-" * 68)
    print(f"ALL CROSS-VERIFIED: {all_cv}")
    print(f"sha256: {digest}")
    print(f"certificate -> {os.path.relpath(OUT, ROOT)}")
    return 0 if all_cv else 1


if __name__ == "__main__":
    sys.exit(main())
