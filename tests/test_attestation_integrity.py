"""Tests for scripts/check_attestation_integrity.py.

This is the local gate that catches the attestation-gap class (an attestation calling a
`def`/`instance` a "theorem", or claiming a declaration absent from source) without an
AXLE run. The committed registry must pass it, and its detectors must actually fire."""
import json
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


def _hash_fixture(tmp_path, *, recorded_hash="correct"):
    (tmp_path / "Brockian").mkdir()
    source = tmp_path / "Brockian" / "HashBound.lean"
    source.write_text(
        "import Mathlib\nnamespace Brockian.HashBound\n"
        "theorem clean : True := by trivial\nend Brockian.HashBound\n"
    )
    receipts = tmp_path / "registry" / "attestations"
    receipts.mkdir(parents=True)
    expected = ci.attest.content_hash(ci.attest._flatten(str(source)))
    payload = {
        "module": "Brockian.HashBound",
        "module_verified": True,
        "declarations": [{
            "name": "Brockian.HashBound.clean",
            "kind": "theorem",
            "axle_verdict": "verified",
            "axioms": [],
            "axioms_ok": True,
        }],
    }
    if recorded_hash is not None:
        payload["content_hash"] = expected if recorded_hash == "correct" else recorded_hash
    receipt = receipts / "HashBound.json"
    receipt.write_text(json.dumps(payload))
    return receipt


def test_matching_content_hash_passes(tmp_path, monkeypatch):
    receipt = _hash_fixture(tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(ci, "ATT_DIR", "registry/attestations")
    assert ci.check() == []

    required = {str(receipt.relative_to(tmp_path))}
    assert ci.check(required) == []


def test_mismatching_content_hash_fails(tmp_path, monkeypatch):
    _hash_fixture(tmp_path, recorded_hash="deadbeefdeadbeef")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(ci, "ATT_DIR", "registry/attestations")

    findings = ci.check()

    assert any("attestation-content-hash-mismatch" in msg for _, msg in findings)


def test_changed_legacy_receipt_requires_hash(tmp_path, monkeypatch):
    receipt = _hash_fixture(tmp_path, recorded_hash=None)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(ci, "ATT_DIR", "registry/attestations")
    assert ci.check() == []  # untouched legacy receipt is grandfathered

    findings = ci.check({str(receipt.relative_to(tmp_path))})

    assert any("attestation-content-hash-missing" in msg for _, msg in findings)


def test_changed_lean_source_maps_to_existing_receipt(tmp_path, monkeypatch):
    receipt = _hash_fixture(tmp_path, recorded_hash=None)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(ci, "ATT_DIR", "registry/attestations")

    required = ci._required_hash_paths(["Brockian/HashBound.lean"])

    assert required == {str(receipt.relative_to(tmp_path))}


def test_unparsed_axioms_fail_unless_explicitly_quarantined(tmp_path, monkeypatch):
    receipt = _hash_fixture(tmp_path)
    payload = json.loads(receipt.read_text())
    payload["declarations"][0]["axioms"] = None
    payload["declarations"][0]["axioms_ok"] = False
    receipt.write_text(json.dumps(payload))
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(ci, "ATT_DIR", "registry/attestations")

    findings = ci.check()
    assert any("attestation-axiom-report-missing" in msg for _, msg in findings)
    assert any("attestation-axioms-not-ok" in msg for _, msg in findings)

    payload["declarations"][0]["verification_quarantine"] = True
    receipt.write_text(json.dumps(payload))
    assert ci.check() == []
