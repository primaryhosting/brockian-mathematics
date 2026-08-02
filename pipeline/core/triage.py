"""Attack queue ordering."""
from __future__ import annotations

from typing import Any

from .schema import ProblemCard
from .stages import triage


def build_attack_queue(cards: list[ProblemCard], limit: int = 20) -> list[dict[str, Any]]:
    """Order cards by triage yield, skip blocked / literature-closed unless re-formalizing."""
    scored: list[dict[str, Any]] = []
    for card in cards:
        if card.status in ("blocked",):
            continue
        plan = triage(card)
        # deprioritize already distilled/proved/literature unless priority high
        if card.status in ("proved", "literature", "distilled", "refuted") and card.priority < 80:
            plan["yield_score"] -= 50
        scored.append(plan)
    scored.sort(key=lambda p: (-p["yield_score"], p["id"]))
    return scored[:limit]
