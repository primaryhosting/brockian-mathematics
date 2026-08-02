"""Pipeline stages: intake → triage → decompose → attack → verify → ledger → distill → publish."""
from __future__ import annotations

from datetime import datetime, timezone
from typing import Any, Optional

from .ledger import AttemptFacts, derive_problem_register, facts_from_card
from .schema import ProblemCard


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def triage(card: ProblemCard) -> dict[str, Any]:
    """Recommend attack modes and yield estimate without mutating the card."""
    modes = list(card.attack_modes) or _default_modes(card)
    formalizable = any(
        t.get("kind") in ("lean_theorem", "lean_def") for t in card.formal_targets if isinstance(t, dict)
    ) or card.domain in ("math", "erdos", "distillation")

    yield_score = card.priority
    # Boost finite / combinatorial tags
    tags = set(card.tags or [])
    if tags & {"finite", "combinatorics", "graph", "equational", "sieve"}:
        yield_score += 10
    if card.difficulty <= 2:
        yield_score += 15
    if card.difficulty >= 5:
        yield_score -= 10
    if card.risk_tier >= 3:
        yield_score -= 20

    plan = {
        "id": card.id,
        "domain": card.domain,
        "status": card.status,
        "recommended_modes": modes,
        "formalizable": formalizable,
        "risk_tier": card.risk_tier,
        "yield_score": yield_score,
        "next_actions": _next_actions(card, modes),
        "warnings": _warnings(card),
    }
    return plan


def _default_modes(card: ProblemCard) -> list[str]:
    d = card.domain
    if d == "distillation":
        return ["distill", "formalize", "refute"]
    if d == "erdos":
        return ["literature", "decompose", "formalize", "compute"]
    if d == "sair":
        return ["literature", "distill", "decompose"]
    if d in ("math",):
        return ["decompose", "formalize", "dual_prover"]
    if d in ("physics", "quantum"):
        return ["decompose", "formalize", "compute"]
    if d == "cs":
        return ["formalize", "compute", "refute"]
    return ["decompose"]


def _next_actions(card: ProblemCard, modes: list[str]) -> list[str]:
    actions: list[str] = []
    if card.status == "open" and "decompose" in modes:
        actions.append("Write reduction plan: lemmas, finite cases, named hypotheses.")
    if "literature" in modes and (card.source or {}).get("external_status") in (None, "unknown", "open"):
        actions.append("Sync external status (erdosproblems / arXiv / SAIR).")
    if "formalize" in modes:
        actions.append("Add formal_targets and Lean scaffold (defs only → SCAFFOLD).")
    if "refute" in modes:
        actions.append("Search counterexamples / dual-prover refutation race.")
    if "compute" in modes:
        actions.append("Small-N compute cert or numeric sanity bounds.")
    if "distill" in modes:
        actions.append("Compress techniques into ≤10KB cheatsheet; run distill-check.")
    if card.risk_tier >= 2:
        actions.append("Human review before public claim (risk_tier ≥ 2).")
    if not actions:
        actions.append("Record attempt with pipeline_cli attempt.")
    return actions


def _warnings(card: ProblemCard) -> list[str]:
    w: list[str] = []
    ext = (card.source or {}).get("external_status")
    if ext == "solved" and card.status not in ("literature", "proved", "refuted"):
        w.append("External source marks solved — prefer LITERATURE unless re-formalizing.")
    if card.status == "proved" and card.verification.get("backend") == "lean_axle":
        w.append("status=proved is not enough; register needs AXLE verified + clean axioms.")
    if card.risk_tier == 3:
        w.append("Tier-3: block public PROVED claims without multi-review.")
    if "RH" in card.title or "riemann" in (card.title or "").lower():
        w.append("RH-class: keep schema/conditional; never overclaim.")
    return w


def record_attempt(
    card: ProblemCard,
    mode: str,
    result: str,
    note: str = "",
    agent: str = "human",
    artifacts: Optional[list[str]] = None,
    axle_verified: Optional[bool] = None,
    axioms_clean: bool = False,
) -> tuple[ProblemCard, str]:
    """Append an attempt and update status + derived register."""
    attempt = {
        "ts": utc_now_iso(),
        "mode": mode,
        "result": result,
        "note": note,
        "agent": agent,
        "artifacts": artifacts or [],
    }
    card.attempts = list(card.attempts or []) + [attempt]

    # Status transitions (conservative)
    status_from_result = {
        "scaffold": "scaffolded",
        "partial": "partial",
        "conditional": "conditional",
        "proved": "proved",  # card status; register still needs AXLE
        "refuted": "refuted",
        "distilled": "distilled",
        "blocked": "blocked",
        "literature": "literature",
        "failed": card.status,  # keep prior
        "open": "open",
    }
    if result in status_from_result and result != "failed":
        card.status = status_from_result[result]

    facts = facts_from_card(card)
    if axle_verified is not None:
        facts.lean_axle_verified = axle_verified
        facts.axioms_clean = axioms_clean
    if result == "proved" and axle_verified is True and axioms_clean:
        facts.lean_axle_verified = True
        facts.axioms_clean = True
    if result == "distilled":
        facts.distill_pass = True
    if result == "scaffold":
        facts.has_scaffold = True
    if mode == "compute" and result in ("partial", "proved"):
        facts.has_compute_cert = True

    reg = derive_problem_register(facts)
    return card, reg


def decompose_stub(card: ProblemCard) -> dict[str, Any]:
    """Lightweight decomposition outline for attack queue docs."""
    return {
        "id": card.id,
        "title": card.title,
        "layers": [
            "0. Precise statement + forbidden overclaims",
            "1. Finite / local / special cases",
            "2. Definitions and scaffolds (SCAFFOLD only)",
            "3. Conditional reductions (named hypotheses)",
            "4. Full attack or refutation",
            "5. Independent verification + ledger",
        ],
        "suggested_lemmas": _suggest_lemmas(card),
    }


def _suggest_lemmas(card: ProblemCard) -> list[str]:
    tags = set(card.tags or [])
    out: list[str] = []
    if "sieve" in tags or card.domain == "math":
        out.append("Local admissibility / singular series positivity for small moduli")
    if "equational" in tags or card.domain == "distillation":
        out.append("Implication vs finite magma counterexample dichotomy")
    if "spectral" in tags or card.domain in ("physics", "quantum"):
        out.append("Symmetric densely-defined operator + limit-point/limit-circle")
    if "graph" in tags or "combinatorics" in tags:
        out.append("Finite configuration check + extremal bound")
    if not out:
        out.append("Isolate the essential difficulty (Erdős acorn vs marshmallow)")
    return out
