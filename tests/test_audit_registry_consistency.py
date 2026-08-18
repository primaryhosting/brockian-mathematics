"""Tests for the registry truth-gate (scripts/audit_registry_consistency.py).

Covers the attestation smell detectors (sorryAx / axioms_ok / axle_verdict /
module_verified), malformed-attestation tolerance, the --strict exit contract,
and the register-invariant re-derivation over registry entries themselves.
Assertions are made on Finding.code and Finding.level, never on message text.
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import audit_registry_consistency as a  # noqa: E402

CLEAN_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


# ── helpers ──────────────────────────────────────────────────────────────────

def _decl(name="Brockian.X.thm_a", **kw):
    d = {
        "name": name,
        "kind": "theorem",
        "axle_verdict": "verified",
        "axioms": list(CLEAN_AXIOMS),
        "axioms_ok": True,
    }
    d.update(kw)
    return d


def _attestation(module="Brockian.X", module_verified=True, declarations=...):
    return {
        "module": module,
        "environment": "lean-4.32.0",
        "module_verified": module_verified,
        "declarations": [_decl()] if declarations is ... else declarations,
    }


def _smells(tmp_path, att, stem="X"):
    root = tmp_path / "Brockian.lean"
    root.write_text(f"import Brockian.{stem}\n")
    attdir = tmp_path / "attestations"
    attdir.mkdir(exist_ok=True)
    (attdir / f"{stem}.json").write_text(json.dumps(att))
    return a.find_attestation_smells(tmp_path, attdir, root)


def _errors(findings, code=None):
    return [
        f for f in findings
        if f.level == "ERROR" and (code is None or f.code == code)
    ]


# ── attestation smell detectors ──────────────────────────────────────────────

def test_sorry_axiom_is_error(tmp_path):
    att = _attestation(declarations=[_decl(axioms=["sorryAx"] + CLEAN_AXIOMS)])
    findings = _smells(tmp_path, att)
    assert len(_errors(findings, "attestation-sorry-axiom")) == 1


def test_axioms_not_ok_is_error(tmp_path):
    att = _attestation(declarations=[_decl(axioms_ok=False)])
    findings = _smells(tmp_path, att)
    assert len(_errors(findings, "attestation-axioms-not-ok")) == 1


def test_axle_failed_is_error(tmp_path):
    att = _attestation(declarations=[_decl(axle_verdict="failed")])
    findings = _smells(tmp_path, att)
    assert len(_errors(findings, "attestation-axle-failed")) == 1


def test_module_unverified_is_error_not_warn(tmp_path):
    findings = _smells(tmp_path, _attestation(module_verified=False))
    unverified = [f for f in findings if f.code == "attestation-unverified"]
    assert len(unverified) == 1
    assert unverified[0].level == "ERROR"


def test_clean_attestation_has_no_error_findings(tmp_path):
    findings = _smells(tmp_path, _attestation())
    assert _errors(findings) == []


def test_null_declarations_no_crash_and_nondict_decls_skipped(tmp_path):
    # declarations: null must not crash and must produce exactly one
    # attestation-declarations ERROR.
    findings = _smells(tmp_path, _attestation(declarations=None))
    assert len(_errors(findings, "attestation-declarations")) == 1
    # Non-dict declaration entries must be skipped without a crash (and a list
    # IS a declarations list, so no attestation-declarations ERROR fires).
    findings2 = _smells(
        tmp_path, _attestation(declarations=["not-a-dict", _decl()]), stem="X"
    )
    assert _errors(findings2, "attestation-declarations") == []
    assert _errors(findings2) == []


# ── register invariants over registry entries themselves ─────────────────────

def _proved_entry(name="Brockian.X.thm_a", **overrides):
    entry = {
        "name": name,
        "kind": "theorem",
        "module": "Brockian.X",
        "statement": "True",
        "source": {"file": "Brockian/X.lean"},
        "register": "PROVED",
        "axioms": list(CLEAN_AXIOMS),
        "flags": {"native_decide": False, "sorry": False, "exact_search": False},
        "verification": {
            "lake_build": "pending",
            "axioms_ok": True,
            "axle": {"verdict": "verified", "environment": "lean-4.32.0"},
        },
        "conditional_rung": None,
        "discharged_by": None,
        "quarantine": False,
        "ledger_run": "r1",
        "provenance_note": "test",
    }
    entry.update(overrides)
    return entry


def test_honest_proved_entry_has_no_invariant_findings():
    assert a.find_register_invariants([_proved_entry()]) == []


def test_proved_with_sorry_axiom_is_error():
    entry = _proved_entry(axioms=["sorryAx"] + CLEAN_AXIOMS)
    assert len(_errors(a.find_register_invariants([entry]), "proved-invariant")) == 1


def test_proved_with_extra_axiom_is_error():
    entry = _proved_entry(axioms=CLEAN_AXIOMS + ["Brockian.secretAxiom"])
    assert len(_errors(a.find_register_invariants([entry]), "proved-invariant")) == 1


def test_proved_with_sorry_flag_is_error():
    entry = _proved_entry(
        flags={"native_decide": False, "sorry": True, "exact_search": False}
    )
    assert len(_errors(a.find_register_invariants([entry]), "proved-invariant")) == 1


def test_proved_with_nonverified_axle_is_error():
    for verdict in ("pending", "failed"):
        entry = _proved_entry(
            verification={
                "lake_build": "pending",
                "axioms_ok": True,
                "axle": {"verdict": verdict, "environment": None},
            }
        )
        assert len(
            _errors(a.find_register_invariants([entry]), "proved-invariant")
        ) == 1


def test_proved_with_conditional_rung_is_error():
    entry = _proved_entry(conditional_rung="classical")
    assert len(_errors(a.find_register_invariants([entry]), "proved-invariant")) == 1


def test_discharged_with_sorry_axiom_is_error():
    entry = _proved_entry(register="DISCHARGED", axioms=["sorryAx"])
    assert len(
        _errors(a.find_register_invariants([entry]), "open-register-sorry")
    ) == 1


def test_conditional_with_sorry_flag_is_error():
    entry = _proved_entry(
        register="CONDITIONAL",
        conditional_rung="classical",
        flags={"native_decide": False, "sorry": True, "exact_search": False},
    )
    assert len(
        _errors(a.find_register_invariants([entry]), "open-register-sorry")
    ) == 1


def test_proved_with_malformed_verification_is_error():
    entry = _proved_entry(verification="verified")  # wrong type
    findings = a.find_register_invariants([entry])
    assert len(_errors(findings, "proved-malformed")) == 1
    # must not crash, and the collapsed axle still fails the verdict leg
    assert _errors(findings, "proved-invariant")


# ── --strict exit contract via main() ────────────────────────────────────────

def _write_main_fixture(tmp_path, module_verified=True):
    root = tmp_path / "Brockian.lean"
    root.write_text("import Brockian.X\n")
    attdir = tmp_path / "attestations"
    attdir.mkdir(exist_ok=True)
    (attdir / "X.json").write_text(
        json.dumps(_attestation(module_verified=module_verified))
    )
    registry = tmp_path / "theorems.json"
    registry.write_text(
        json.dumps({"theorems": [_proved_entry()], "summary": {"PROVED": 1}})
    )
    verdicts = tmp_path / "verdicts.yaml"  # deliberately absent
    return registry, verdicts, root, attdir


def _run_main(monkeypatch, registry, verdicts, root, attdir):
    # Override ALL four path args: the defaults resolve to the live repo, whose
    # registry currently yields real ERROR findings.
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "audit_registry_consistency.py",
            "--strict",
            "--registry", str(registry),
            "--provenance", str(verdicts),
            "--root-imports", str(root),
            "--attestations", str(attdir),
        ],
    )
    return a.main()


def test_strict_exits_nonzero_on_error(tmp_path, monkeypatch):
    fixture = _write_main_fixture(tmp_path, module_verified=False)
    assert _run_main(monkeypatch, *fixture) == 1


def test_strict_exits_zero_when_clean(tmp_path, monkeypatch):
    fixture = _write_main_fixture(tmp_path, module_verified=True)
    assert _run_main(monkeypatch, *fixture) == 0
