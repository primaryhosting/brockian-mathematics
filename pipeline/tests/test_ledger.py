"""Unit tests for derive_problem_register."""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO))

from pipeline.core.ledger import AttemptFacts, derive_problem_register  # noqa: E402


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
