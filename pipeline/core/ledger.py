"""Derive problem-level registers from attempt facts (never hand-assert PROVED).

Mirrors scripts/gen_registry.derive_register spirit at the problem-card layer.
Theorem-level PROVED still lives in registry/theorems.json via attest + AXLE.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional

# Problem-level registers (see design §3)
REGISTERS = (
    "OPEN",
    "SCAFFOLD",
    "CONDITIONAL",
    "COMPUTATION",
    "DISTILLED",
    "PROVED",
    "REFUTED",
    "DISCHARGED",
    "BLOCKED",
    "LITERATURE",
    "PARTIAL",
)


@dataclass
class AttemptFacts:
    """Facts used to derive a problem register."""

    status_field: str = "open"  # card.status
    latest_result: Optional[str] = None  # last attempt.result
    backend: str = "hybrid"
    lean_axle_verified: Optional[bool] = None  # True only after AXLE verified
    axioms_clean: bool = False
    has_scaffold: bool = False
    has_compute_cert: bool = False
    distill_pass: bool = False  # size + accuracy gates
    literature_accepted: bool = False
    dual_prover_disagree: bool = False
    theater_flagged: bool = False
    conditional: bool = False
    discharged: bool = False
    attempt_results: list[str] = field(default_factory=list)


def derive_problem_register(f: AttemptFacts) -> str:
    """Compute register from facts. Precedence is intentional and unit-tested.

    Precedence (high wins):
      BLOCKED      — theater or dual-prover disagreement
      REFUTED      — certified counterexample
      PROVED       — Lean path: axioms clean + AXLE verified only
      DISCHARGED   — prior conditional closed
      DISTILLED    — distillation harness pass
      LITERATURE   — external solution accepted (not our formal proof)
      CONDITIONAL  — proved under named hypothesis
      COMPUTATION  — finite / numeric certificate
      SCAFFOLD     — defs / schemas only
      PARTIAL      — incomplete progress
      OPEN         — default
    """
    if f.theater_flagged or f.dual_prover_disagree:
        return "BLOCKED"

    results = list(f.attempt_results)
    if f.latest_result:
        results.append(f.latest_result)
    results_set = set(results)

    if f.latest_result == "refuted" or "refuted" in results_set:
        return "REFUTED"

    # PROVED only via formal independent verification — never from status alone
    if f.backend in ("lean_axle", "hybrid") and f.lean_axle_verified is True and f.axioms_clean:
        return "PROVED"
    if f.latest_result == "proved" and f.lean_axle_verified is not True:
        # Attempt claimed proved without AXLE → not PROVED
        if f.conditional:
            return "CONDITIONAL"
        if f.has_compute_cert:
            return "COMPUTATION"
        return "PARTIAL"

    if f.discharged:
        return "DISCHARGED"

    if f.distill_pass or f.latest_result == "distilled":
        return "DISTILLED"

    if f.literature_accepted or f.latest_result == "literature" or f.status_field == "literature":
        return "LITERATURE"

    if f.conditional or f.latest_result == "conditional" or f.status_field == "conditional":
        return "CONDITIONAL"

    if f.has_compute_cert or f.latest_result == "partial" and f.backend == "compute":
        if f.has_compute_cert:
            return "COMPUTATION"

    if f.has_scaffold or f.latest_result == "scaffold" or f.status_field == "scaffolded":
        return "SCAFFOLD"

    if f.status_field == "partial" or f.latest_result == "partial" or f.latest_result == "failed":
        if f.latest_result == "failed" and f.status_field == "open":
            return "OPEN"
        if f.status_field == "partial" or f.latest_result == "partial":
            return "PARTIAL"

    if f.status_field == "blocked" or f.latest_result == "blocked":
        return "BLOCKED"

    if f.status_field == "open" or not results:
        return "OPEN"

    # Map remaining status field
    status_map = {
        "proved": "PARTIAL",  # without axle → not PROVED
        "refuted": "REFUTED",
        "distilled": "DISTILLED",
        "scaffolded": "SCAFFOLD",
        "conditional": "CONDITIONAL",
        "literature": "LITERATURE",
        "blocked": "BLOCKED",
        "partial": "PARTIAL",
        "open": "OPEN",
    }
    return status_map.get(f.status_field, "OPEN")


def facts_from_card(card: Any) -> AttemptFacts:
    """Build AttemptFacts from a ProblemCard-like object."""
    attempts = getattr(card, "attempts", None) or []
    latest = attempts[-1] if attempts else None
    latest_result = latest.get("result") if isinstance(latest, dict) else None
    results = [a.get("result") for a in attempts if isinstance(a, dict) and a.get("result")]
    ver = getattr(card, "verification", None) or {}
    backend = ver.get("backend", "hybrid") if isinstance(ver, dict) else "hybrid"
    notes = (getattr(card, "notes", "") or "").lower()
    status = getattr(card, "status", "open")

    has_scaffold = status == "scaffolded" or any(
        t.get("kind") in ("lean_def", "lean_theorem") for t in (getattr(card, "formal_targets", None) or [])
        if isinstance(t, dict)
    )
    has_compute = any(
        t.get("kind") == "compute_cert" for t in (getattr(card, "formal_targets", None) or [])
        if isinstance(t, dict)
    ) or any(a.get("mode") == "compute" and a.get("result") in ("partial", "proved") for a in attempts if isinstance(a, dict))

    literature = status == "literature" or (
        (getattr(card, "source", None) or {}).get("external_status") == "solved"
        and backend == "literature"
    )

    return AttemptFacts(
        status_field=status,
        latest_result=latest_result,
        backend=backend,
        lean_axle_verified=None,  # filled by attempt hooks / registry join
        axioms_clean=False,
        has_scaffold=has_scaffold and status in ("scaffolded", "partial", "open", "conditional"),
        has_compute_cert=has_compute,
        distill_pass=status == "distilled" or latest_result == "distilled",
        literature_accepted=literature,
        dual_prover_disagree="disagree" in notes,
        theater_flagged="theater" in notes or status == "blocked",
        conditional=status == "conditional" or latest_result == "conditional",
        discharged=False,
        attempt_results=[r for r in results if r],
    )


def summarize_ledger(cards: list[Any], axle_by_id: Optional[dict[str, bool]] = None) -> list[dict[str, Any]]:
    """Produce ledger rows for all cards."""
    axle_by_id = axle_by_id or {}
    rows = []
    for card in cards:
        facts = facts_from_card(card)
        if card.id in axle_by_id:
            facts.lean_axle_verified = axle_by_id[card.id]
            facts.axioms_clean = True
        reg = derive_problem_register(facts)
        rows.append(
            {
                "id": card.id,
                "domain": card.domain,
                "title": card.title,
                "status": card.status,
                "register": reg,
                "difficulty": getattr(card, "difficulty", None),
                "priority": getattr(card, "priority", 50),
                "risk_tier": getattr(card, "risk_tier", 1),
                "backend": facts.backend,
                "attempts": len(getattr(card, "attempts", None) or []),
                "tags": getattr(card, "tags", None) or [],
            }
        )
    # sort: priority desc, difficulty asc, id
    rows.sort(key=lambda r: (-int(r.get("priority") or 0), int(r.get("difficulty") or 3), r["id"]))
    return rows
