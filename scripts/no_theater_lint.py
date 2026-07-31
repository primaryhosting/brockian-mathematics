"""No-theater lint: flag the failure signatures the intake ledger named, independent of
the build (spec 4). Advisory for most; blocking on sorry/admit inside closed modules.

Patterns (each a named ledger failure mode):
  - placeholder operator: `:= 0` on something later asserted self-adjoint       (mode: placeholder)
  - R-mod collapse:        `% (2 * π)` / `% (2*Real.pi)`                          (mode: r_mod_collapse)
  - Nat-division exponent: `^ (1 / 2)` etc. with integer literals               (mode: nat_div_exponent)
  - True-typed Prop field / statement-only Prop = True                          (mode: true_field)
  - holes:                 `sorry`, `admit`                                     (mode: hole)

Usage:
    python3 scripts/no_theater_lint.py Brockian/*.lean [--closed Core Admissibility ...]
Exit non-zero iff a BLOCKING finding exists (hole in a closed module).
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass

# (mode, compiled regex, human message)
PATTERNS = [
    ("r_mod_collapse", re.compile(r"%\s*\(\s*2\s*\*\s*(π|Real\.pi)"),
     "phase written with real `%` collapses to 0 (ℝ-mod); use an explicit winding term"),
    ("nat_div_exponent", re.compile(r"\^\s*\(?\s*1\s*/\s*2\s*\)?"),
     "fractional exponent `^(1/2)` in ℕ elaborates to 0; use ((1:ℝ)/2) or Real.sqrt"),
    ("true_field", re.compile(r":\s*Prop\s*:=\s*True\b|:=\s*True\b.*--.*(field|obligation)"),
     "Prop field filled with `True` — instance-filled theater; never citable"),
    ("placeholder_zero", re.compile(r":=\s*0\b.*(Laplacian|laplacian|Operator|operator|Hamiltonian|hamiltonian)"),
     "operator defined `:= 0` then asserted self-adjoint — placeholder theater"),
]
HOLE = re.compile(r"\b(sorry|admit)\b")
# Comment-aware: strip line comments before hole scan to avoid the run-69 false positive
# (the word "sorry" appearing in a comment).
COMMENT = re.compile(r"--.*$")


@dataclass
class Finding:
    file: str
    line: int
    mode: str
    message: str
    blocking: bool


def _module_name(path: str) -> str:
    base = path.replace("\\", "/").split("/")[-1]
    return base[:-5] if base.endswith(".lean") else base


def lint_text(path: str, text: str, closed: set[str]) -> list[Finding]:
    findings: list[Finding] = []
    is_closed = _module_name(path) in closed
    for i, raw in enumerate(text.splitlines(), start=1):
        for mode, rx, msg in PATTERNS:
            if rx.search(raw):
                findings.append(Finding(path, i, mode, msg, blocking=False))
        code = COMMENT.sub("", raw)
        if HOLE.search(code):
            findings.append(Finding(path, i, "hole", "sorry/admit present",
                                    blocking=is_closed))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--closed", nargs="*", default=[],
                    help="module names that are fully closed (holes there are blocking)")
    args = ap.parse_args()
    closed = set(args.closed)
    all_findings: list[Finding] = []
    for path in args.files:
        try:
            text = open(path, encoding="utf-8").read()
        except OSError:
            continue
        all_findings.extend(lint_text(path, text, closed))
    for f in all_findings:
        tag = "BLOCK" if f.blocking else "warn "
        print(f"[{tag}] {f.file}:{f.line}  {f.mode}: {f.message}")
    blocking = [f for f in all_findings if f.blocking]
    print(f"\n{len(all_findings)} findings, {len(blocking)} blocking")
    return 1 if blocking else 0


if __name__ == "__main__":
    sys.exit(main())
