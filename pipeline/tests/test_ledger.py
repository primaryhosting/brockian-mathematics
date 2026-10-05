"""Unit tests for derive_problem_register."""
from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

_REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO))

from pipeline.core.ledger import (  # noqa: E402
    AttemptFacts,
    derive_problem_register,
    facts_from_card,
    registry_evidence_for_cards,
    summarize_ledger,
)
from pipeline.core.schema import ProblemCard  # noqa: E402
from pipeline.core.stages import record_attempt  # noqa: E402


def test_open_default():
    assert derive_problem_register(AttemptFacts()) == "OPEN"


def test_blocked_theater():
    assert derive_problem_register(AttemptFacts(theater_flagged=True)) == "BLOCKED"


def test_blocked_dual_disagree():
    assert derive_problem_register(AttemptFacts(dual_prover_disagree=True)) == "BLOCKED"


def test_refuted():
    assert derive_problem_register(AttemptFacts(latest_result="refuted")) == "REFUTED"


def test_proved_requires_axle():
    # Claim proved without axle → not PROVED
    reg = derive_problem_register(
        AttemptFacts(latest_result="proved", lean_axle_verified=None, axioms_clean=False)
    )
    assert reg != "PROVED"


def test_proved_with_axle():
    reg = derive_problem_register(
        AttemptFacts(
            backend="lean_axle",
            lean_axle_verified=True,
            axioms_clean=True,
            latest_result="proved",
        )
    )
    assert reg == "PROVED"


def test_distilled():
    assert derive_problem_register(AttemptFacts(distill_pass=True)) == "DISTILLED"


def test_literature():
    assert derive_problem_register(AttemptFacts(literature_accepted=True)) == "LITERATURE"


def test_scaffold():
    assert derive_problem_register(AttemptFacts(has_scaffold=True, status_field="scaffolded")) == "SCAFFOLD"


def test_conditional():
    assert derive_problem_register(AttemptFacts(conditional=True)) == "CONDITIONAL"


def test_computation():
    assert derive_problem_register(AttemptFacts(has_compute_cert=True)) == "COMPUTATION"


def test_discharged():
    assert derive_problem_register(AttemptFacts(discharged=True)) == "DISCHARGED"


def test_attempt_verification_survives_round_trip_and_later_failure_revokes_it():
    card = ProblemCard(
        id="math-verification",
        domain="math",
        title="Verification persistence",
        statement="Exercise structured attempt evidence.",
        verification={"backend": "lean_axle"},
    )
    card, register = record_attempt(
        card,
        mode="formalize",
        result="proved",
        axle_verified=True,
        axioms_clean=True,
    )
    persisted = ProblemCard.from_dict(card.to_dict())
    facts = facts_from_card(persisted)
    assert persisted.attempts[-1]["axle_verified"] is True
    assert persisted.attempts[-1]["axioms_clean"] is True
    assert facts.lean_axle_verified is True
    assert facts.axioms_clean is True
    assert register == "PROVED"

    persisted, register = record_attempt(
        persisted,
        mode="formalize",
        result="failed",
        axle_verified=False,
    )
    facts = facts_from_card(persisted)
    assert facts.lean_axle_verified is False
    assert facts.axioms_clean is False
    assert register == "PARTIAL"


def _registry_row(name: str, *, register: str = "PROVED", axle: str = "verified", axioms: bool = True):
    return {
        "name": name,
        "register": register,
        "verification": {
            "axioms_ok": axioms,
            "axle": {"verdict": axle},
        },
    }


def _card_with_refs(*refs: str, status: str = "proved"):
    return SimpleNamespace(
        id="math-registry-join",
        domain="math",
        title="Registry join",
        status=status,
        difficulty=3,
        priority=50,
        risk_tier=1,
        tags=[],
        notes="",
        source={},
        formal_targets=[],
        verification={"backend": "lean_axle"},
        attempts=[
            {
                "result": "proved",
                "axle_verified": True,
                "axioms_clean": True,
            }
        ],
        ledger_refs=list(refs),
    )


def test_registry_join_requires_every_reference():
    card = _card_with_refs("Theorem.good", "Theorem.missing")
    evidence = registry_evidence_for_cards(
        [card], {"theorems": [_registry_row("Theorem.good")]}
    )
    row = summarize_ledger([card], registry_by_id=evidence)[0]
    assert row["register"] == "PARTIAL"
    assert row["verification"]["axle_verified"] is False
    assert row["verification"]["missing_registry_refs"] == ["Theorem.missing"]


@pytest.mark.parametrize(
    "registry_row",
    [
        _registry_row("Theorem.target", register="PARTIAL"),
        _registry_row("Theorem.target", axle="failed"),
        _registry_row("Theorem.target", axioms=False),
    ],
)
def test_registry_join_rejects_unproved_unverified_or_unclean_theorem(registry_row):
    card = _card_with_refs("Theorem.target")
    evidence = registry_evidence_for_cards([card], {"theorems": [registry_row]})
    row = summarize_ledger([card], registry_by_id=evidence)[0]
    assert row["register"] == "PARTIAL"
    assert row["verification"]["unverified_registry_refs"] == ["Theorem.target"]


def test_registry_join_proves_scoped_claim_but_not_partial_card():
    registry = {"theorems": [_registry_row("Theorem.target")]}
    proved_card = _card_with_refs("Theorem.target")
    evidence = registry_evidence_for_cards([proved_card], registry)
    row = summarize_ledger([proved_card], registry_by_id=evidence)[0]
    assert row["register"] == "PROVED"

    partial_card = _card_with_refs("Theorem.target", status="partial")
    partial_card.attempts = []
    evidence = registry_evidence_for_cards([partial_card], registry)
    row = summarize_ledger([partial_card], registry_by_id=evidence)[0]
    assert row["register"] != "PROVED"
