"""Tests for scripts/check_attestation_integrity.py.

This is the local gate that catches the attestation-gap class (an attestation calling a
`def`/`instance` a "theorem", or claiming a declaration absent from source) without an
AXLE run. The committed registry must pass it, and its detectors must actually fire."""
import sys

sys.path.insert(0, "scripts")
import check_attestation_integrity as ci  # noqa: E402


def test_committed_registry_is_clean():
    findings = ci.check()
    assert findings == [], f"expected clean, got {findings[:5]}"


def test_declared_recognizes_declaration_keywords():
    src = ("namespace N\n"
           "theorem t : True := trivial\n"
           "def d := 1\n"
           "noncomputable def N.q := 2\n"
           "instance i : Inhabited Nat := ⟨0⟩\n"
           "end N\n")
    assert ci._declared(src, "t")
    assert ci._declared(src, "d")
    assert ci._declared(src, "q")        # namespace-prefixed def
    assert ci._declared(src, "i")        # instance
    assert not ci._declared(src, "absent")


def test_class_split_proof_vs_data():
    assert ci._class_of("theorem") == ci._class_of("lemma") == "proof"
    for k in ("def", "abbrev", "structure", "class", "inductive", "conjecture"):
        assert ci._class_of(k) == "data"
