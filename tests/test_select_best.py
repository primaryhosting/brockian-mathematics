from __future__ import annotations

import importlib.util
import pathlib


MODULE_PATH = pathlib.Path(__file__).parents[1] / "aristotle" / "select_best.py"
SPEC = importlib.util.spec_from_file_location("select_best", MODULE_PATH)
assert SPEC and SPEC.loader
select_best = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(select_best)


def test_gate_requires_both_hash_matched_positive_receipts():
    proof_hash = "abc"
    axle = {"hash": proof_hash, "verified": True}
    axiom = {"hash": proof_hash, "trusted": True}

    assert select_best.candidate_gate(proof_hash, axle, axiom) == "verified"
    assert select_best.candidate_gate(proof_hash, axle, None) == "unknown"
    assert (
        select_best.candidate_gate(
            proof_hash, axle, {"hash": "stale", "trusted": False}
        )
        == "unknown"
    )


def test_hash_matched_failure_rejects_candidate():
    proof_hash = "abc"
    assert (
        select_best.candidate_gate(
            proof_hash,
            {"hash": proof_hash, "verified": False},
            {"hash": proof_hash, "trusted": True},
        )
        == "rejected"
    )


def test_unknown_alternative_replaces_rejected_winner():
    rejected = {
        "gate": "rejected",
        "compiles": True,
        "axiom_clean": True,
        "lines": 5,
        "project_id": "a",
    }
    unknown = {
        "gate": "unknown",
        "compiles": None,
        "axiom_clean": True,
        "lines": 50,
        "project_id": "b",
    }

    assert min([rejected, unknown], key=select_best.candidate_score) is unknown


def test_verified_candidate_beats_shorter_untested_candidate():
    verified = {
        "gate": "verified",
        "compiles": True,
        "axiom_clean": True,
        "lines": 80,
        "project_id": "a",
    }
    unknown = {
        "gate": "unknown",
        "compiles": True,
        "axiom_clean": True,
        "lines": 5,
        "project_id": "b",
    }

    assert min([verified, unknown], key=select_best.candidate_score) is verified
