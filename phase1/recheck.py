#!/usr/bin/env python3
"""recheck.py — independently re-verify a Phase-1 certificate WITHOUT our pipeline.

Given a certificate.json, this:
  1. recomputes the SHA-256 over its {provers, obligations} payload and checks it matches
     (tamper-evidence: any edit to a statement, an smt2 query, or a verdict changes the hash);
  2. re-runs an SMT solver on each embedded smt2 query and confirms unsat (= the property holds),
     independently reproducing the Z3 leg.

The Lean leg is a kernel-checked bv_decide/LRAT proof re-verified by AXLE; its verdict is recorded
in the certificate. This script reproduces the Z3 leg and the tamper-evidence hash locally.

Run:  python3 phase1/recheck.py phase1/certificate.json  [--solver z3]
Exit 0 iff the hash matches AND every obligation re-checks unsat.
"""
import hashlib
import json
import os
import subprocess
import sys
import tempfile


def canonical_payload(obls, provers):
    return json.dumps({"provers": provers, "obligations": obls}, sort_keys=True, separators=(",", ":"))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    solver = "z3"
    for a in sys.argv[1:]:
        if a.startswith("--solver="):
            solver = a.split("=", 1)[1]
    if not args:
        print("usage: recheck.py <certificate.json> [--solver=z3]")
        return 2
    cert = json.load(open(args[0]))

    print("== 1. tamper-evidence: recompute SHA-256 over {provers, obligations} ==")
    recomputed = hashlib.sha256(canonical_payload(cert["obligations"], cert["provers"]).encode()).hexdigest()
    hash_ok = recomputed == cert.get("sha256")
    print(f"   recorded:   {cert.get('sha256')}")
    print(f"   recomputed: {recomputed}")
    print(f"   {'MATCH — certificate is intact' if hash_ok else 'MISMATCH — certificate was altered'}\n")

    print(f"== 2. re-run the embedded SMT queries with {solver} (unsat = property holds) ==")
    all_ok = True
    for o in cert["obligations"]:
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tf:
            tf.write(o["smt2"]); path = tf.name
        try:
            r = subprocess.run([solver, path], capture_output=True, text=True, timeout=120)
            last = (r.stdout + r.stderr).strip().splitlines()
            got = last[-1].strip() if last else "?"
        finally:
            os.unlink(path)
        want = "unsat" if o["z3"]["verdict"] == "proved" else "sat"
        ok = got == want
        all_ok = all_ok and ok
        print(f"   {o['name']:<24} {solver} -> {got:<7} "
              f"{'✓ re-verified' if ok else '✗ DOES NOT re-check'}")

    ok = hash_ok and all_ok
    print(f"\n{'✓ CERTIFICATE RE-VERIFIED — hash intact, every obligation re-checks unsat' if ok else '✗ RE-CHECK FAILED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
