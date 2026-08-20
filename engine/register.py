"""engine.register — the single derived-register gate.

The register is DERIVED, never hand-asserted, from three inputs:
  * build-derived facts: axioms, flags (native_decide / sorry / exact_search)
  * external attestation: the AXLE independent verdict
  * provenance map: conditional_rung

This is the one definition of PROVED. It replaces the forward derivation that lived in
`scripts/gen_registry.py` and the criterion re-checked by the two validators
(`scripts/audit_registry_consistency.py`, `scripts/verify_firewall.py`). Those callers
import `derive` here instead of carrying their own copy.

`derive` is a PURE function of a small facts record — no I/O, no knowledge of which
register (theorems.json vs domains.json) a proof belongs to. Routing is the caller's job.
The whole-registry DISCHARGED post-pass stays in gen_registry and calls `derive` for the
base classification. pipeline's richer problem-level vocabulary
(BLOCKED/REFUTED/DISTILLED/…) also calls `derive` for the shared
PROVED/CONDITIONAL/COMPUTATION sub-decision and keeps its own states around it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from engine.verify import ALLOWED_AXIOMS

VALID_RUNGS = {"classical", "literature", "open"}


@dataclass
class Flags:
    native_decide: bool = False
    sorry: bool = False
    exact_search: bool = False


@dataclass
class DeclFacts:
    name: str
    kind: str  # "theorem" | "lemma" | "def" | "abbrev" | "conjecture"
    axioms: list = field(default_factory=list)
    flags: Flags = field(default_factory=Flags)
    axle_verified: Optional[bool] = None  # None = not yet checked
    conditional_rung: Optional[str] = None  # classical | literature | open


def derive(f: DeclFacts) -> str:
    """Compute the register from build facts + AXLE verdict + rung.

    Precedence:
      CONJECTURE  — a def / Prop container (not a theorem/lemma)
      DEFINITION  — a def / abbrev
      CONDITIONAL — depends on a named hypothesis (conditional_rung set)
      COMPUTATION — relies on decide / native_decide finite checks
      PROVED      — sorry-free, axioms ⊆ allowed, no native_decide/exact?,
                    AND an independent AXLE verdict == verified
    A declaration that would be PROVED but fails any leg falls back to COMPUTATION (if
    native_decide) else is reported UNVERIFIED so it can never masquerade as proved.
    """
    if f.kind == "conjecture":
        return "CONJECTURE"
    if f.kind in ("def", "abbrev"):
        return "DEFINITION"
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
