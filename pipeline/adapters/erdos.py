"""Erdős problems adapter — erdosproblems.com style cards."""
from __future__ import annotations

from pipeline.core.schema import ProblemCard


def make_erdos_card(
    number: int,
    title: str,
    statement: str,
    *,
    external_status: str = "open",
    tags: list[str] | None = None,
    difficulty: int = 4,
    priority: int = 50,
    notes: str = "",
) -> ProblemCard:
    status = "literature" if external_status == "solved" else "open"
    backend = "literature" if external_status == "solved" else "hybrid"
    return ProblemCard(
        id=f"erdos-{number}",
        domain="erdos",
        title=title,
        statement=statement,
        status=status,
        source={
            "url": f"https://www.erdosproblems.com/{number}",
            "citation": f"Erdős problem {number}",
            "external_status": external_status,
        },
        difficulty=difficulty,
        tags=tags or ["erdos"],
        formal_targets=[],
        attack_modes=["literature", "decompose", "formalize", "compute", "refute"],
        verification={
            "backend": backend,
            "criteria": [
                "Do not claim PROVED without Lean+AXLE or accepted literature formalization",
                "AI prose solutions without independent check → BLOCKED",
            ],
        },
        risk_tier=1 if external_status != "solved" else 1,
        notes=notes,
        priority=priority,
    )
