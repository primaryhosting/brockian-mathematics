import json
import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import gen_registry as g  # noqa: E402

CLEAN = ["propext", "Classical.choice", "Quot.sound"]


def facts(**kw):
    kw.setdefault("name", "t")
    kw.setdefault("kind", "theorem")
    flags = g.Flags(**kw.pop("flags", {}))
    return g.DeclFacts(flags=flags, **kw)


def test_proved_requires_all_three_legs():
    f = facts(axioms=CLEAN, axle_verified=True)
    assert g.derive_register(f) == "PROVED"


def test_clean_axioms_but_axle_unverified_is_not_proved():
    assert g.derive_register(facts(axioms=CLEAN, axle_verified=None)) == "UNVERIFIED"
    assert g.derive_register(facts(axioms=CLEAN, axle_verified=False)) == "UNVERIFIED"


def test_extra_axiom_blocks_proved():
    f = facts(axioms=CLEAN + ["sorryAx"], axle_verified=True)
    assert g.derive_register(f) == "UNVERIFIED"


def test_native_decide_is_computation():
    f = facts(axioms=CLEAN, axle_verified=True, flags={"native_decide": True})
    assert g.derive_register(f) == "COMPUTATION"


def test_sorry_flag_blocks_proved():
    f = facts(axioms=CLEAN, axle_verified=True, flags={"sorry": True})
    assert g.derive_register(f) == "UNVERIFIED"


def test_exact_search_blocks_proved():
    f = facts(axioms=CLEAN, axle_verified=True, flags={"exact_search": True})
    assert g.derive_register(f) == "UNVERIFIED"


def test_conditional_rung_wins_over_proved():
    f = facts(axioms=CLEAN, axle_verified=True, conditional_rung="classical")
    assert g.derive_register(f) == "CONDITIONAL"


def test_invalid_rung_raises():
    with pytest.raises(ValueError):
        g.derive_register(facts(axioms=CLEAN, conditional_rung="bogus"))


def test_def_is_definition():
    assert g.derive_register(facts(kind="def", axioms=CLEAN, axle_verified=True)) == "DEFINITION"


def test_prop_container_is_conjecture():
    assert g.derive_register(facts(kind="conjecture", axioms=CLEAN)) == "CONJECTURE"


def test_build_entry_records_verification_block():
    e = g.build_entry(
        facts(name="Brockian.q_minus_two", axioms=CLEAN, axle_verified=True),
        prov={"module": "Brockian.Admissibility", "quarantine": True, "ledger_run": "74"},
        source={"file": "Brockian/Admissibility.lean", "line": 1},
        statement="...", axle_env="lean-4.32.0",
    )
    assert e["register"] == "PROVED"
    assert e["verification"]["axle"] == {"verdict": "verified", "environment": "lean-4.32.0"}
    assert e["quarantine"] is True


def _write_attestation(attestations, stem, module, module_verified=True,
                       decl_name=None, verdict="verified"):
    (attestations / f"{stem}.json").write_text(json.dumps({
        "module": module,
        "environment": "lean-4.32.0",
        "module_verified": module_verified,
        "declarations": [{
            "name": decl_name or f"{module}.thm_a",
            "kind": "theorem",
            "axle_verdict": verdict,
            "axioms": CLEAN,
        }],
    }))


def test_unverified_module_demotes_stale_verified_decl(tmp_path, monkeypatch):
    """A sorry-backed module (module_verified: false) whose decls carry a stale
    per-decl "verified" stamp must regenerate as UNVERIFIED, never PROVED
    (the ConstellationSpectralFinal failure mode, upstream)."""
    (tmp_path / "Brockian.lean").write_text("import Brockian.Spectral\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    _write_attestation(attestations, "Spectral", "Brockian.Spectral",
                       module_verified=False)
    monkeypatch.chdir(tmp_path)

    reg = g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))

    (entry,) = reg["theorems"]
    assert entry["register"] == "UNVERIFIED"
    assert entry["verification"]["axle"]["verdict"] == "pending"
    assert reg["summary"] == {"UNVERIFIED": 1}


def test_stray_attestation_without_root_import_is_skipped(tmp_path, monkeypatch):
    """Attestation files not backed by an `import Brockian.<stem>` in the root
    (stray parallel-tool output) must contribute zero entries."""
    (tmp_path / "Brockian.lean").write_text("import Brockian.Real\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    _write_attestation(attestations, "Real", "Brockian.Real")
    _write_attestation(attestations, "Stray", "Brockian.Stray")  # no root import
    monkeypatch.chdir(tmp_path)

    reg = g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))

    assert [e["name"] for e in reg["theorems"]] == ["Brockian.Real.thm_a"]
    assert reg["summary"] == {"PROVED": 1}


def test_kind_override_demotes_to_conjecture(tmp_path, monkeypatch):
    """A verdicts.yaml per-decl kind_override must demote an AXLE-verified
    theorem to CONJECTURE."""
    (tmp_path / "Brockian.lean").write_text("import Brockian.Weyl\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    _write_attestation(attestations, "Weyl", "Brockian.Weyl",
                       decl_name="Brockian.Weyl.big_claim")
    verdicts = tmp_path / "verdicts.yaml"
    verdicts.write_text(
        "runs:\n"
        "  r1:\n"
        "    module: Brockian.Weyl\n"
        "    overrides:\n"
        "      - name: big_claim\n"
        "        kind_override: conjecture\n"
    )
    monkeypatch.chdir(tmp_path)

    reg = g.generate(str(attestations), str(verdicts))

    (entry,) = reg["theorems"]
    assert entry["register"] == "CONJECTURE"
    assert entry["kind"] == "conjecture"


def test_generate_uses_attestation_stem_for_source_path(tmp_path, monkeypatch):
    (tmp_path / "Brockian.lean").write_text("import Brockian.BrocardGapConjecture\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    (attestations / "BrocardGapConjecture.json").write_text(json.dumps({
        "module": "Brockian.BrocardGap",
        "environment": "lean-4.32.0",
        "module_verified": True,
        "declarations": [{
            "name": "Brockian.BrocardGap.brocard_3_5",
            "kind": "theorem",
            "axle_verdict": "verified",
            "axioms": CLEAN,
        }],
    }))
    monkeypatch.chdir(tmp_path)

    registry = g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))

    assert registry["theorems"][0]["source"] == {
        "file": "Brockian/BrocardGapConjecture.lean"
    }


# ── DISCHARGED post-pass: unambiguous discharged_by resolution ───────────────

def _write_module(attestations, stem, module, decl_short):
    (attestations / f"{stem}.json").write_text(json.dumps({
        "module": module,
        "environment": "lean-4.32.0",
        "module_verified": True,
        "declarations": [{
            "name": f"{module}.{decl_short}",
            "kind": "theorem",
            "axle_verdict": "verified",
            "axioms": CLEAN,
        }],
    }))


def _discharge_fixture(tmp_path, discharged_by, extra_proved_modules):
    """One CONDITIONAL decl in Brockian.Cond whose discharged_by is given, plus
    PROVED modules each exposing a theorem with short name `thm_x`."""
    imports = ["import Brockian.Cond\n"]
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    _write_module(attestations, "Cond", "Brockian.Cond", "needs_hyp")
    for stem in extra_proved_modules:
        imports.append(f"import Brockian.{stem}\n")
        _write_module(attestations, stem, f"Brockian.{stem}", "thm_x")
    (tmp_path / "Brockian.lean").write_text("".join(imports))
    verdicts = tmp_path / "verdicts.yaml"
    verdicts.write_text(
        "runs:\n"
        "  r1:\n"
        "    module: Brockian.Cond\n"
        "    conditional_rung: classical\n"
        f"    discharged_by: {discharged_by}\n"
    )
    return attestations, verdicts


def _cond_entry(reg):
    (entry,) = [e for e in reg["theorems"] if e["module"] == "Brockian.Cond"]
    return entry


def test_discharge_by_unique_short_name(tmp_path, monkeypatch):
    attestations, verdicts = _discharge_fixture(tmp_path, "thm_x", ["P1"])
    monkeypatch.chdir(tmp_path)
    reg = g.generate(str(attestations), str(verdicts))
    assert _cond_entry(reg)["register"] == "DISCHARGED"


def test_ambiguous_short_name_stays_conditional_with_warning(tmp_path, monkeypatch,
                                                             capsys):
    attestations, verdicts = _discharge_fixture(tmp_path, "thm_x", ["P1", "P2"])
    monkeypatch.chdir(tmp_path)
    reg = g.generate(str(attestations), str(verdicts))
    assert _cond_entry(reg)["register"] == "CONDITIONAL"
    captured = capsys.readouterr()
    assert "ambiguous" in captured.err
    assert captured.out == ""  # warning goes to stderr, stdout stays clean


def test_discharge_by_non_proved_name_stays_conditional(tmp_path, monkeypatch):
    attestations, verdicts = _discharge_fixture(tmp_path, "no_such_thm", ["P1"])
    monkeypatch.chdir(tmp_path)
    reg = g.generate(str(attestations), str(verdicts))
    assert _cond_entry(reg)["register"] == "CONDITIONAL"


def test_discharge_by_full_name_wins_despite_short_collision(tmp_path, monkeypatch):
    attestations, verdicts = _discharge_fixture(
        tmp_path, "Brockian.P1.thm_x", ["P1", "P2"])
    monkeypatch.chdir(tmp_path)
    reg = g.generate(str(attestations), str(verdicts))
    assert _cond_entry(reg)["register"] == "DISCHARGED"


# ── malformed attestations fail LOUD, naming the offending file ──────────────

def test_attestation_missing_declarations_raises_with_filename(tmp_path, monkeypatch):
    (tmp_path / "Brockian.lean").write_text("import Brockian.Bad\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    (attestations / "Bad.json").write_text(json.dumps({
        "module": "Brockian.Bad",
        "module_verified": True,
    }))
    monkeypatch.chdir(tmp_path)
    with pytest.raises(ValueError, match="Bad.json"):
        g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))


def test_truncated_attestation_json_raises_with_filename(tmp_path, monkeypatch):
    (tmp_path / "Brockian.lean").write_text("import Brockian.Trunc\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    (attestations / "Trunc.json").write_text('{"module": "Brockian.Trunc", "decl')
    monkeypatch.chdir(tmp_path)
    with pytest.raises(ValueError, match="Trunc.json"):
        g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))


def test_declaration_missing_name_raises_with_filename(tmp_path, monkeypatch):
    (tmp_path / "Brockian.lean").write_text("import Brockian.NoName\n")
    attestations = tmp_path / "registry" / "attestations"
    attestations.mkdir(parents=True)
    (attestations / "NoName.json").write_text(json.dumps({
        "module": "Brockian.NoName",
        "module_verified": True,
        "declarations": [{"kind": "theorem", "axle_verdict": "verified"}],
    }))
    monkeypatch.chdir(tmp_path)
    with pytest.raises(ValueError, match="NoName.json"):
        g.generate(str(attestations), str(tmp_path / "missing-verdicts.yaml"))
