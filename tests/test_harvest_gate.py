import json
import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import harvest_gate
import autolab_wave68


def declaration(name: str, *, quarantined: bool = False) -> dict:
    value = {
        "name": name,
        "kind": "theorem",
        "axle_verdict": "verified",
        "axioms": ["propext"],
        "axioms_ok": True,
    }
    if quarantined:
        value["verification_quarantine"] = True
        value["verification_quarantine_reason"] = "AXIOM_EVIDENCE_PENDING"
    return value


def report(*declarations: dict, content_hash: str = "fresh-hash") -> dict:
    return {
        "module": "Brockian.X",
        "environment": "lean-4.32.2",
        "module_verified": True,
        "content_hash": content_hash,
        "declarations": list(declarations),
    }


def test_partial_report_merge_preserves_siblings_and_quarantine():
    trusted = declaration("Brockian.X.trusted")
    quarantined = declaration("Brockian.X.quarantined", quarantined=True)
    old = report(trusted, quarantined, content_hash="old-hash")
    fresh = report(declaration("Brockian.X.new"))

    merged = harvest_gate.merge_attestation_reports(old, fresh)

    assert merged["content_hash"] == "fresh-hash"
    assert [d["name"] for d in merged["declarations"]] == [
        "Brockian.X.trusted",
        "Brockian.X.quarantined",
        "Brockian.X.new",
    ]
    assert merged["declarations"][0] == trusted
    assert merged["declarations"][1] == quarantined


def test_fresh_clean_evidence_can_replace_its_own_quarantine_only():
    untouched = declaration("Brockian.X.untouched", quarantined=True)
    refreshed = declaration("Brockian.X.refreshed", quarantined=True)
    old = report(untouched, refreshed, content_hash="old-hash")
    fresh = report(declaration("Brockian.X.refreshed"))

    merged = harvest_gate.merge_attestation_reports(old, fresh)
    by_name = {d["name"]: d for d in merged["declarations"]}

    assert by_name["Brockian.X.untouched"]["verification_quarantine"] is True
    assert "verification_quarantine" not in by_name["Brockian.X.refreshed"]


def test_unknown_axioms_are_rejected_before_merge():
    bad = declaration("Brockian.X.unknown")
    bad["axioms"] = None
    bad["axioms_ok"] = False

    try:
        harvest_gate.merge_attestation_reports(None, report(bad))
    except ValueError as exc:
        assert "lacks clean evidence" in str(exc)
    else:  # pragma: no cover - assertion branch
        raise AssertionError("unknown axiom evidence was accepted")


def test_atomic_json_write_replaces_complete_payload(tmp_path):
    path = tmp_path / "receipt.json"
    path.write_text('{"old": true}\n')
    payload = report(declaration("Brockian.X.new"))

    harvest_gate.atomic_json_write(str(path), payload)

    assert json.loads(path.read_text()) == payload
    assert not list(tmp_path.glob("*.tmp"))


def test_reconcile_archives_only_named_terminal_attempts(tmp_path, monkeypatch):
    terminal = "Brockian.XiFunctionalEquation.riemannXi_zero_quartet#B"
    fresh = "Brockian.QuantumFiniteSpectral.unitary_conj_spectrum_eq"
    state = {
        "pending": {terminal: "old-pid", fresh: "fresh-pid"},
        "attempt_outcomes": {},
        "done": {},
    }
    (tmp_path / "aristotle_state.json").write_text(json.dumps(state))
    monkeypatch.setenv("AUTOLAB_DATA_DIR", str(tmp_path))

    archived, preserved = autolab_wave68.reconcile_aristotle_state()
    result = json.loads((tmp_path / "aristotle_state.json").read_text())

    assert archived == 1
    assert preserved == 1
    assert result["pending"] == {fresh: "fresh-pid"}
    assert result["attempt_outcomes"][terminal]["pid"] == "old-pid"
