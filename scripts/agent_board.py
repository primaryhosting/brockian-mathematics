#!/usr/bin/env python3
"""Shared multi-agent status board (Claude / Codex / Grok).

Prints: git branch, tip, dirty paths classified by likely owner, registry summary,
and Gate-1 package readiness. Read-only — safe for all agents.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Path prefixes → suggested owner (heuristic for collab, not ACL)
OWNER_HINTS = [
    (("Brockian/Weyl", "Brockian/WeylWeak", "Brockian/WeylKato", "Brockian/WeylFree",
      "Brockian/WeylSchrodinger", "Brockian/WeylLimit", "Brockian/WeylBridge",
      "Brockian/WeylOperator", "Brockian/WeylPlancherel", "Brockian/WeylResolvent",
      "aristotle/kato", "aristotle/weak-regularity", "aristotle/bounded"), "Claude/Codex Weyl"),
    (("Brockian/Franklin", "Brockian/Pentagonal", "Brockian/OddDistinct",
      "aristotle/franklin"), "Claude Franklin/partition"),
    (("Brockian/Admissibility", "Brockian/Goldbach", "Brockian/Singular",
      "Brockian/Sieve", "Brockian/Cos", "Brockian/Twin", "Brockian/D5",
      "Brockian/Galois", "Brockian/Metallic"), "Grok finite/sieve (or free)"),
    (("pipeline/", "docs/partner/", "docs/MULTI-AGENT", "docs/PROGRAM-REPORT",
      "docs/SETTLE", "scripts/agent_board", "scripts/pipeline_", "scripts/gen_program",
      "scripts/settle", "scripts/refute"), "Grok pipeline/partner"),
    (("docs/AGENT-COORDINATION",), "shared (append-only)"),
    (("registry/", "REGISTRY.md", "observatory/", "Brockian.lean", "paper/"), "integrator (owner of ship)"),
]


def run(cmd: list[str]) -> str:
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return (r.stdout or "") + (r.stderr or "")


def classify(path: str) -> str:
    for prefixes, owner in OWNER_HINTS:
        if any(path.startswith(p) or p in path for p in prefixes):
            return owner
    return "unclaimed / any"


def main() -> int:
    print("=== agent_board (read-only) ===")
    print("root:", ROOT)
    print()
    print("--- git ---")
    print(run(["git", "status", "--short", "--branch"]).rstrip() or "(clean)")
    print()
    print(run(["git", "log", "--oneline", "-5"]).rstrip())
    print()

    status = run(["git", "status", "--porcelain"])
    dirty = []
    for line in status.splitlines():
        if not line.strip():
            continue
        path = line[3:].strip()
        if " -> " in path:
            path = path.split(" -> ", 1)[-1]
        dirty.append((line[:2].strip(), path, classify(path)))

    if dirty:
        print("--- dirty by owner hint ---")
        by: dict[str, list[str]] = {}
        for code, path, owner in dirty:
            by.setdefault(owner, []).append(f"{code:2} {path}")
        for owner, rows in sorted(by.items()):
            print(f"\n[{owner}]")
            for r in rows:
                print(" ", r)
    else:
        print("--- dirty: none ---")

    print()
    print("--- registry summary ---")
    tj = ROOT / "registry" / "theorems.json"
    if tj.is_file():
        data = json.loads(tj.read_text(encoding="utf-8"))
        summary = data.get("summary") or {}
        for k in sorted(summary.keys()):
            print(f"  {k}: {summary[k]}")
        # Gate-1 package presence
        names = {t.get("name", "") for t in data.get("theorems") or []}
        checks = [
            "Brockian.WeylWeakPrimitiveLocal.weakToPrimitiveRegularity_of_distributional_primitives",
            "Brockian.Weyl.KatoResolventConstruction.essentiallySelfAdjoint_perturb_of_unitShiftRightResolvents_norm_lt_one",
        ]
        print()
        print("--- Gate-1 collab package in registry? ---")
        for c in checks:
            print(f"  {'YES' if c in names else 'NO '}  {c.split('.')[-1]}")
    else:
        print("  (no theorems.json)")

    print()
    print("--- Gate-1 files on disk ---")
    for rel in [
        "Brockian/WeylWeakPrimitiveLocal.lean",
        "Brockian/WeylKatoResolventConstruction.lean",
        "registry/attestations/WeylWeakPrimitiveLocal.json",
        "registry/attestations/WeylKatoResolventConstruction.json",
    ]:
        p = ROOT / rel
        print(f"  {'OK' if p.is_file() else 'MISSING'}  {rel}")

    print()
    print("Collab protocol: docs/MULTI-AGENT-COLLAB.md")
    print("Claims log:      docs/AGENT-COORDINATION.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
