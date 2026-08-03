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
