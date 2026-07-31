"""Generate registry/theorems.json from the compiled environment + AXLE verdicts +
provenance/verdicts.yaml.

The register is DERIVED (never hand-asserted) from three inputs (spec 5):
  - build-derived: axioms, flags (native_decide / sorry / exact_search)
  - external attestation: the AXLE independent verdict
  - provenance-map: conditional_rung (and ledger_run / quarantine / provenance_note)

`derive_register` is the load-bearing rule and is unit-tested in isolation. The rest of
this module wires extraction + merge + artifact emission and is exercised end-to-end once
the Lean core builds.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VALID_RUNGS = {"classical", "literature", "open"}


@dataclass
class Flags:
    native_decide: bool = False
    sorry: bool = False
    exact_search: bool = False


@dataclass
class DeclFacts:
    name: str
    kind: str  # "theorem" | "lemma" | "def"
    axioms: list[str] = field(default_factory=list)
    flags: Flags = field(default_factory=Flags)
    axle_verified: Optional[bool] = None  # None = not yet checked
    conditional_rung: Optional[str] = None  # classical | literature | open


def derive_register(f: DeclFacts) -> str:
    """Compute the register from build facts + AXLE verdict + rung (spec 4).

    Precedence:
      CONJECTURE  — a def / Prop container (not a theorem/lemma)
      CONDITIONAL — depends on a named hypothesis (conditional_rung set)
      COMPUTATION — relies on decide / native_decide finite checks
      PROVED      — sorry-free, axioms ⊆ allowed, no native_decide/exact?,
                    AND an independent AXLE verdict == verified
    A declaration that would be PROVED but fails any leg falls back to COMPUTATION
    (if native_decide) else is reported UNVERIFIED so it can never masquerade as proved.
    """
    if f.kind not in ("theorem", "lemma"):
        return "CONJECTURE"
    if f.conditional_rung is not None:
        if f.conditional_rung not in VALID_RUNGS:
            raise ValueError(f"{f.name}: invalid conditional_rung {f.conditional_rung!r}")
        return "CONDITIONAL"
    if f.flags.native_decide:
        return "COMPUTATION"
    axioms_ok = set(f.axioms).issubset(ALLOWED_AXIOMS)
    clean = axioms_ok and not f.flags.sorry and not f.flags.exact_search
    if clean and f.axle_verified is True:
        return "PROVED"
    return "UNVERIFIED"


def build_entry(f: DeclFacts, prov: dict[str, Any], source: dict[str, Any],
                statement: str, axle_env: Optional[str]) -> dict[str, Any]:
    register = derive_register(f)
    return {
        "name": f.name,
        "kind": f.kind,
        "module": prov.get("module", ""),
        "statement": statement,
        "source": source,
        "register": register,
        "axioms": sorted(f.axioms),
        "flags": {
            "native_decide": f.flags.native_decide,
            "sorry": f.flags.sorry,
            "exact_search": f.flags.exact_search,
        },
        "verification": {
            "lake_build": "green",
            "axioms_ok": set(f.axioms).issubset(ALLOWED_AXIOMS),
            "axle": {
                "verdict": ("verified" if f.axle_verified is True
                            else "failed" if f.axle_verified is False else "pending"),
                "environment": axle_env,
            },
        },
        "conditional_rung": f.conditional_rung,
        "quarantine": bool(prov.get("quarantine", False)),
        "ledger_run": prov.get("ledger_run"),
        "provenance_note": prov.get("provenance_note"),
    }
