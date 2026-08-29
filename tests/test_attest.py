import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import attest


def test_attestation_stem_uses_source_file_not_namespace_tail():
    assert attest._attestation_stem("Brockian/WeylHarmonicOscillator.lean") == \
        "WeylHarmonicOscillator"


def test_kind_of_parent_structure_not_shadowed_by_nested_theorem():
    src = """
structure Factorization where
  value : Nat

theorem Factorization.isCompactOperator (F : Factorization) : True := by
  trivial
"""
    assert attest._kind_of(src, "Factorization") == "def"
    assert attest._kind_of(src, "Factorization.isCompactOperator") == "theorem"


def test_kind_of_parent_def_not_shadowed_by_nested_def():
    src = """
def CompactResolvent : Prop := True
def CompactResolvent.witness : Nat := 0
"""
    assert attest._kind_of(src, "CompactResolvent") == "conjecture"
    assert attest._kind_of(src, "CompactResolvent.witness") == "def"


def test_axioms_for_distinguishes_explicit_empty_from_unparseable():
    name = "Brockian.X.clean"
    assert attest._axioms_for(
        [f"declaration '{name}' does not depend on any axioms"], name) == []
    assert attest._axioms_for(
        [f"declaration '{name}' depends on axioms: [propext, Classical.choice]"],
        name,
    ) == ["propext", "Classical.choice"]
    assert attest._axioms_for(
        [f"declaration '{name}' depends on axioms: [propext,\n"
         " Classical.choice,\n Quot.sound]"],
        name,
    ) == ["propext", "Classical.choice", "Quot.sound"]
    assert attest._axioms_for(
        [f"declaration '{name}' axioms were omitted by the service"], name) is None
    assert attest._axioms_for([], name) is None


def test_attestation_complete_requires_parsed_axiom_evidence():
    base = {
        "module_verified": True,
        "declarations": [{
            "name": "Brockian.X.clean",
            "kind": "theorem",
            "axle_verdict": "verified",
            "axioms": [],
            "axioms_ok": True,
        }],
    }
    assert attest.attestation_complete(base)

    base["declarations"][0]["axioms"] = None
    assert not attest.attestation_complete(base)
    base["declarations"][0]["axioms"] = []
    base["declarations"][0]["verification_quarantine"] = True
    assert not attest.attestation_complete(base)
