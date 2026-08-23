from __future__ import annotations

import copy
import sys
from pathlib import Path

import yaml

sys.path.insert(0, "scripts")
import validate_reference_spines as validator  # noqa: E402


MANIFEST = Path("provenance/reference-spines/grinberg-graph-theory-v3.yaml")


def _document() -> dict:
    return yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))


def test_committed_reference_spine_is_clean():
    assert validator.validate_path(MANIFEST) == []


def test_classical_slice_cannot_enter_novelty_ledger():
    doc = _document()
    doc["slices"][0]["novelty_ledger"] = True
    errors = validator.validate_document(doc, validator.load_registry(), "fixture")
    assert any("excluded tag CLASSICAL_REFERENCE" in error for error in errors)


def test_registry_verified_slice_must_resolve_green_declarations():
    doc = _document()
    fixture = copy.deepcopy(doc["slices"][0])
    fixture["declarations"] = ["Brockian.DoesNotExist.theorem"]
    doc["slices"] = [fixture]
    errors = validator.validate_document(doc, validator.load_registry(), "fixture")
    assert any("registry declaration is not green" in error for error in errors)


def test_queued_slice_cannot_claim_a_declaration():
    doc = _document()
    queued = next(item for item in doc["slices"] if item["implementation_status"] == "queued")
    queued["declarations"] = ["Brockian.Fake.claim"]
    errors = validator.validate_document(doc, validator.load_registry(), "fixture")
    assert any("queued slices must not claim declarations" in error for error in errors)


def test_pending_slice_must_advance_after_registry_promotion():
    doc = _document()
    pending = next(
        item for item in doc["slices"] if item["implementation_status"] == "lean_source_pending_axle"
    )
    declaration = pending["declarations"][0]
    registry = validator.load_registry()
    registry[declaration] = "PROVED"
    errors = validator.validate_document(doc, registry, "fixture")
    assert any("advance status explicitly" in error for error in errors)
