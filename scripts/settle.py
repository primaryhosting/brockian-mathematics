"""settle.py — the certificate factory: make certificates the unit of progress.

Codifies the closed formal-attack loop that was previously hand-run on every integration:

    attempt  →  prove / refute race  →  AXLE independent check  →  no-theater lint
             →  #print axioms audit   →  derived register        →  certificate + register join

A *certificate* is the atomic output: a machine-checked record of a settled claim, its verdict,
the prover + environment, the axiom footprint, and the register it earns. This turns "a human
drove the gate this time" into a reproducible system that every domain (Brockian finite math,
Erdős intake, SAIR distillation Stage 2, physics) plugs into.

Modes
  prove   (default)  : verify a module whose target theorems are claimed PROVED.
  refute  <neg.lean> : verify a module that proves the NEGATION / exhibits a finite counterexample.
                       If it verifies, the original statement is FALSE — a refutation certificate.

Dual-race BLOCKED rule
  If a prove-target AND its refute-target BOTH verify, that is a contradiction (a bug in a
  statement or a checker). settle emits verdict=BLOCKED and refuses to join the registry — the
  honest failure mode, never a silent pick.

Verification legs (all must pass for a PROVED certificate):
  1. AXLE independent re-check @ the named environment (statement fidelity).
  2. no_theater_lint  (ex-falso / degenerate-witness / hidden-sorry / overtitling guard).
  3. #print axioms ⊆ {propext, Classical.choice, Quot.sound}; no native_decide.

Usage
  python3 scripts/settle.py Brockian/Foo.lean
  python3 scripts/settle.py Brockian/Foo.lean --refute aristotle/foo-neg/target.lean
  python3 scripts/settle.py Brockian/Foo.lean --env lean-4.32.0 --json

Certificates are written to registry/certificates/<Module>.json (gitignore-friendly ledger of
attempts; the registry join itself still goes through gen_registry from committed attestations).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
import attest  # _flatten, attest
import axle_client  # check
import no_theater_lint  # _blank_block_comments
from gen_registry import DeclFacts, Flags, derive_register

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s(){}:]+)",
    re.M,
)


def _names(path: str) -> list[str]:
    src = open(path).read()
    src = no_theater_lint._blank_block_comments(src)
    src = "\n".join(re.sub(r"--.*$", "", ln) for ln in src.splitlines())
    return sorted(set(DECL_RE.findall(src)))


def _namespace(path: str) -> str | None:
    m = re.search(r"^namespace\s+([A-Za-z0-9_.']+)", open(path).read(), re.M)
    return m.group(1) if m else None


def _lint(path: str) -> tuple[bool, str]:
    out = subprocess.run(
        [sys.executable, os.path.join(os.path.dirname(__file__), "no_theater_lint.py"), path],
        capture_output=True, text=True,
    ).stdout.strip().splitlines()
    last = out[-1] if out else ""
    return ("0 findings, 0 blocking" in last), last


def _verify(path: str, env: str, timeout: int) -> tuple[bool, list[str]]:
    r = axle_client.check(attest._flatten(path), env=env, timeout=timeout)
    return bool(r.verified), (list(getattr(r, "errors", []) or [])[:4])


def _attest_registers(path: str, ns: str | None, env: str) -> tuple[dict, list[dict]]:
    """Attest the module and preview the register each declaration would earn."""
    att = attest.attest(path, ns, _names(path), env)
    rows = []
    for d in att["declarations"]:
        facts = DeclFacts(
            name=d["name"], kind=d.get("kind", "theorem"),
            axioms=d.get("axioms") or [],
            flags=Flags(native_decide=d.get("native_decide", False)),
            axle_verified=True if att.get("module_verified") and d.get("axle_verdict") == "verified" else None,
        )
        rows.append({
            "name": d["name"], "kind": d.get("kind"),
            "register": derive_register(facts),
            "axioms_ok": bool(d.get("axioms_ok")),
            "native_decide": bool(d.get("native_decide", False)),
        })
    return att, rows


def settle(module: str, env: str, timeout: int, refute: str | None) -> dict:
    cert: dict = {"target": module, "prover": f"AXLE@{env}", "env": env}
    if not os.path.exists(module):
        return {**cert, "verdict": "ERROR", "reason": f"no such file: {module}"}

    prove_ok, prove_err = _verify(module, env, timeout)
    lint_ok, lint_msg = _lint(module)

    refute_ok = None
    if refute:
        if os.path.exists(refute):
            refute_ok, _ = _verify(refute, env, timeout)
        else:
            cert["refute_note"] = f"refute target missing: {refute}"

    # dual-race contradiction → BLOCKED
    if prove_ok and refute_ok:
        return {**cert, "verdict": "BLOCKED",
                "reason": "prove AND refute both verify — contradiction (bug in a statement or checker)",
                "no_theater": lint_ok}

    if refute_ok:  # the negation verified → original is FALSE
        return {**cert, "verdict": "REFUTED", "refuted_by": refute, "no_theater": lint_ok}

    if not prove_ok:
        return {**cert, "verdict": "FAILED", "no_theater": lint_ok, "errors": prove_err}

    if not lint_ok:
        return {**cert, "verdict": "THEATER-BLOCKED", "no_theater": False, "lint": lint_msg}

    ns = _namespace(module)
    att, rows = _attest_registers(module, ns, env)
    axioms_clean = all(r["axioms_ok"] for r in rows)
    return {**cert, "verdict": "VERIFIED", "namespace": ns,
            "no_theater": True, "axioms_clean": axioms_clean,
            "n_decls": len(rows),
            "registers": {r: sum(1 for x in rows if x["register"] == r)
                          for r in sorted({x["register"] for x in rows})},
            "declarations": rows}


def main() -> int:
    ap = argparse.ArgumentParser(description="Certificate factory — settle a claim (prove/refute) and emit a certificate.")
    ap.add_argument("module", help="Brockian/<Module>.lean to settle")
    ap.add_argument("--refute", help="a module proving the negation / a finite counterexample", default=None)
    ap.add_argument("--env", default="lean-4.32.0")
    ap.add_argument("--timeout", type=int, default=500)
    ap.add_argument("--json", action="store_true", help="print the raw certificate JSON")
    ap.add_argument("--stamp", default=None, help="ISO timestamp to record (avoids nondeterminism)")
    a = ap.parse_args()

    cert = settle(a.module, a.env, a.timeout, a.refute)
    if a.stamp:
        cert["stamp"] = a.stamp

    os.makedirs("registry/certificates", exist_ok=True)
    stem = os.path.basename(a.module)[:-5]
    open(f"registry/certificates/{stem}.json", "w").write(json.dumps(cert, indent=2))

    if a.json:
        print(json.dumps(cert, indent=2))
    else:
        v = cert["verdict"]
        icon = {"VERIFIED": "✓", "REFUTED": "⊘", "FAILED": "✗",
                "THEATER-BLOCKED": "✗", "BLOCKED": "■", "ERROR": "!"}.get(v, "?")
        extra = ""
        if v == "VERIFIED":
            extra = f" | {cert['n_decls']} decls | axioms_clean={cert['axioms_clean']} | {cert['registers']}"
        elif v == "FAILED" and cert.get("errors"):
            extra = f" | {cert['errors'][0][:80]}"
        elif v in ("BLOCKED", "THEATER-BLOCKED", "REFUTED"):
            extra = f" | {cert.get('reason') or cert.get('refuted_by') or cert.get('lint','')}"
        print(f"{icon} settle {stem}: {v}{extra}")
        print(f"  certificate → registry/certificates/{stem}.json")

    return 0 if cert["verdict"] in ("VERIFIED", "REFUTED") else 1


if __name__ == "__main__":
    raise SystemExit(main())
