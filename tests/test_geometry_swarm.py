from __future__ import annotations

import sys
from pathlib import Path

import yaml

sys.path.insert(0, "scripts")
import geometry_swarm_plan as planner  # noqa: E402
import validate_geometry_swarm as validator  # noqa: E402


BENCHMARK = Path("benchmarks/classical-geometry-swarm.yaml")


def _document() -> dict:
    return yaml.safe_load(BENCHMARK.read_text(encoding="utf-8"))


def test_committed_geometry_swarm_is_clean():
    assert validator.validate_path(BENCHMARK) == []


def test_track_cannot_enter_novelty_ledger():
    document = _document()
    document["tracks"][0]["novelty_ledger"] = True
    errors = validator.validate_document(document, validator.load_registry(), "fixture")
    assert any("novelty_ledger must be false" in error for error in errors)


def test_source_anchor_must_resolve_to_a_source_card():
    document = _document()
    document["tracks"][0]["source_anchors"][0]["source_id"] = "missing-source"
    errors = validator.validate_document(document, validator.load_registry(), "fixture")
    assert any("source_id does not resolve" in error for error in errors)


def test_duplicate_source_pdf_is_rejected():
    document = _document()
    duplicate = dict(document["sources"][0])
    duplicate["id"] = "same-pdf-under-a-second-name"
    duplicate["uploaded_filename"] = "duplicate.pdf"
    document["sources"].append(duplicate)
    errors = validator.validate_document(document, validator.load_registry(), "fixture")
    assert any("pdf_sha256 duplicates" in error for error in errors)


def test_manifold_sources_and_tracks_are_registered():
    document = _document()
    source_ids = {source["id"] for source in document["sources"]}
    track_ids = {track["id"] for track in document["tracks"]}
    assert {
        "cattaneo-notes-on-manifolds-2018",
        "hitchin-differentiable-manifolds-2014",
        "viaclovsky-introduction-to-manifolds-and-geometry-2022",
    } <= source_ids
    assert {
        "atlas-transition-cocycle",
        "real-line-bundle-cocycle-mobius",
        "exterior-derivative-square-zero",
        "finite-quotient-descent",
        "discrete-to-de-rham-comparison-firewall",
    } <= track_ids


def test_baseline_must_remain_green():
    document = _document()
    registry = validator.load_registry()
    declaration = document["tracks"][0]["existing_baseline"]["declarations"][0]
    registry[declaration] = "CONJECTURE"
    errors = validator.validate_document(document, registry, "fixture")
    assert any("existing_baseline declaration is not green" in error for error in errors)


def test_queued_work_cannot_claim_a_future_declaration():
    document = _document()
    document["tracks"][1]["proposed_declarations"] = ["Brockian.Future.Ceva"]
    errors = validator.validate_document(document, validator.load_registry(), "fixture")
    assert any("proposed_declarations must be empty" in error for error in errors)


def test_plan_has_all_five_roles_and_a_promotion_gate():
    document = _document()
    packet = planner.task_packet(document, document["tracks"][1])
    assert [task["role"] for task in packet["tasks"]] == [
        "Explorer",
        "Specifier",
        "Prover",
        "Adversary",
        "Auditor",
    ]
    assert packet["novelty_ledger"] is False
    assert "No promotion" in packet["promotion_gate"]
