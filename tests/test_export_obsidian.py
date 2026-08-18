"""Tests for scripts/export_obsidian.py (tmp vault — never the real USB
volume) and the conveyor's guarded, non-blocking knowledge-graph leg."""
import importlib.util
import json
import os

import pytest

from aristotle import conveyor

_SPEC = importlib.util.spec_from_file_location(
    "export_obsidian",
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                 "scripts", "export_obsidian.py"))
export_obsidian = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(export_obsidian)


@pytest.fixture(autouse=True)
def _no_real_conveyor_log(tmp_path, monkeypatch):
    """conveyor.log() appends to the real aristotle/conveyor.log; the leg
    tests below must never write there (this bit once on 2026-08-18: two
    test-artifact 'USB volume stalled' lines landed in the live log)."""
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "conveyor-test.log"))


# ------------------------------------------------------------------ fixtures

def _registry():
    def entry(name, module, register="PROVED", statement="", note="",
              lake="pending", axle="verified", src=None):
        return {
            "name": name, "kind": "theorem", "module": module,
            "statement": statement,
            "source": {"file": src or module.replace(".", "/") + ".lean"},
            "register": register,
            "verification": {
                "lake_build": lake, "axioms_ok": True,
                "axle": {"verdict": axle, "environment": "lean-4.32.0"},
            },
            "provenance_note": note,
        }
    return {
        "generated_from": "test",
        "summary": {"PROVED": 3, "DEFINITION": 1},
        "theorems": [
            entry("Brockian.Alpha.thm_one", "Brockian.Alpha",
                  statement="Every widget is a gadget.",
                  note="pentagonal structure result"),
            entry("Brockian.Alpha.thm_two", "Brockian.Alpha"),
            entry("Brockian.Beta.thm", "Brockian.Beta",
                  note="spectral CosTrace bound"),
            entry("Brockian.Gamma.defn", "Brockian.Gamma",
                  register="DEFINITION"),  # no PROVED → no note
        ],
    }


@pytest.fixture
def world(tmp_path):
    """tmp repo side (registry + attestations + lean sources) + tmp vault."""
    reg_path = tmp_path / "theorems.json"
    reg_path.write_text(json.dumps(_registry()))
    attest = tmp_path / "attestations"
    attest.mkdir()
    (attest / "Alpha.json").write_text(
        json.dumps({"module": "Brockian.Alpha", "module_verified": True}))
    src = tmp_path / "src"
    (src / "Brockian").mkdir(parents=True)
    (src / "Brockian" / "Alpha.lean").write_text(
        "import Mathlib\nimport Brockian.Beta\n\ntheorem x : True := trivial\n")
    (src / "Brockian" / "Beta.lean").write_text("theorem y : True := trivial\n")
    vault = tmp_path / "vault"
    (vault / "wiki").mkdir(parents=True)
    (vault / "wiki" / "log.md").write_text("# Log\n\n## 2026-05-05\n\n- init\n")
    return {"registry": str(reg_path), "attest": str(attest),
            "src": str(src), "vault": str(vault), "tmp": tmp_path}


def _run(world, **kw):
    return export_obsidian.export(
        registry_path=world["registry"], vault=world["vault"],
        attest_dir=world["attest"], src_root=world["src"],
        budget=kw.pop("budget", 60), **kw)


# ------------------------------------------------------------------ exporter

def test_one_note_per_proved_module_plus_index(world):
    res = _run(world)
    reg_dir = os.path.join(world["vault"], "wiki", "registry")
    assert res["status"] == "ok" and res["errors"] == 0
    # index + Alpha + Beta; Gamma has no PROVED theorem → no note
    assert res["written"] == 3
    assert os.path.exists(os.path.join(reg_dir, "index.md"))
    assert os.path.exists(os.path.join(reg_dir, "modules", "Brockian.Alpha.md"))
    assert os.path.exists(os.path.join(reg_dir, "modules", "Brockian.Beta.md"))
    assert not os.path.exists(
        os.path.join(reg_dir, "modules", "Brockian.Gamma.md"))


def test_module_note_frontmatter_body_and_wikilinks(world):
    _run(world)
    note = open(os.path.join(world["vault"], "wiki", "registry", "modules",
                             "Brockian.Alpha.md")).read()
    assert note.startswith("---\n")
    assert "module: Brockian.Alpha" in note
    assert "status: PROVED" in note
    assert "attestation_date: 20" in note  # ISO date from attestation mtime
    assert "lake_build_pending: 2" in note
    assert "Every widget is a gadget." in note        # statement summary
    assert "`Brockian.Alpha.thm_one`" in note         # theorem list
    assert "[[Brockian.Beta]]" in note                # dependency wikilink
    assert "[[lean4-formalization]]" in note          # concept wikilink
    assert "[[pentagonal-law]]" in note               # keyword concept
    # honest posture, never conflated with lake-built
    assert "AXLE-attested" in note and "pending" in note


def test_no_attestation_file_is_stated_not_invented(world):
    _run(world)
    note = open(os.path.join(world["vault"], "wiki", "registry", "modules",
                             "Brockian.Beta.md")).read()
    assert "attestation_date: unknown" in note
    assert "attestation_date_source: none" in note


def test_index_reports_honest_counts_and_posture(world):
    _run(world)
    idx = open(os.path.join(world["vault"], "wiki", "registry",
                            "index.md")).read()
    assert "Registry entries: **4**" in idx
    assert "PROVED: **3**" in idx           # from the registry summary
    assert "AXLE-attested declarations: **4** of 4" in idx
    assert "lake_build pending: **4**" in idx
    assert "NOT" in idx and "lake-built" in idx  # posture stated plainly
    assert "[[Brockian.Alpha]]" in idx and "[[Brockian.Beta]]" in idx


def test_idempotent_second_run_writes_and_logs_nothing(world):
    first = _run(world)
    assert first["written"] == 3 and first["log_appended"]
    log_after_first = open(
        os.path.join(world["vault"], "wiki", "log.md")).read()
    second = _run(world)
    assert second["written"] == 0
    assert second["unchanged"] == 3
    assert second["log_appended"] is False
    assert open(os.path.join(world["vault"], "wiki",
                             "log.md")).read() == log_after_first


def test_registry_change_rewrites_only_changed_notes(world):
    _run(world, now_date="2026-08-18")
    reg = _registry()
    reg["theorems"][2]["provenance_note"] = "spectral CosTrace bound SHARPENED"
    with open(world["registry"], "w") as fh:
        fh.write(json.dumps(reg))
    res = _run(world, now_date="2026-08-18")
    # Beta changed; Alpha unchanged; index unchanged (same counts, same date)
    assert res["written"] == 1 and res["unchanged"] == 2
    note = open(os.path.join(world["vault"], "wiki", "registry", "modules",
                             "Brockian.Beta.md")).read()
    assert "SHARPENED" in note


def test_log_is_append_only(world):
    _run(world)
    log = open(os.path.join(world["vault"], "wiki", "log.md")).read()
    assert log.startswith("# Log\n\n## 2026-05-05\n\n- init\n")  # preserved
    assert "Registry knowledge-graph export: 3 note(s) written" in log


def test_unmounted_vault_is_an_honest_skip_not_an_error(world):
    res = export_obsidian.export(
        registry_path=world["registry"],
        vault=str(world["tmp"] / "not-mounted"),
        attest_dir=world["attest"], src_root=world["src"], budget=60)
    assert res["status"] == "skipped"
    assert "not mounted" in res["skipped_reason"]
    assert res["written"] == 0


def test_exhausted_budget_reports_partial_honestly(world):
    res = _run(world, budget=-1)  # deadline already passed
    assert res["status"] == "partial"
    assert res["written"] == 0
    assert res["remaining"] == 3  # nothing silently dropped


def test_main_exits_zero_on_skip_and_prints_summary(world, capsys):
    rc = export_obsidian.main([
        "--registry", world["registry"],
        "--vault", str(world["tmp"] / "not-mounted")])
    assert rc == 0
    out = capsys.readouterr().out
    assert "status=skipped" in out


def test_main_reports_broken_registry_as_error(world, capsys):
    rc = export_obsidian.main([
        "--registry", str(world["tmp"] / "missing.json"),
        "--vault", world["vault"]])
    assert rc == 1
    assert "export_obsidian: error" in capsys.readouterr().out


# ------------------------------------------------------- conveyor wiring leg

def test_conveyor_leg_records_runner_result(monkeypatch):
    calls = []

    def runner(name, args, timeout=None):
        calls.append((name, args, timeout))
        return conveyor.StageResult(name=name, status="ok", rc=0,
                                    tail="export_obsidian: status=ok")
    res = conveyor.run_obsidian_export(runner=runner, timeout=42)
    assert res == {"ran": True, "status": "ok",
                   "tail": "export_obsidian: status=ok"}
    assert calls == [("export_obsidian", ["scripts/export_obsidian.py"], 42)]


def test_conveyor_leg_never_raises(monkeypatch):
    def runner(name, args, timeout=None):
        raise RuntimeError("USB volume stalled")
    res = conveyor.run_obsidian_export(runner=runner)
    assert res["ran"] is True and res["status"] == "error"
    assert "stalled" in res["tail"]


def test_conveyor_leg_kill_switch(monkeypatch):
    monkeypatch.setenv("CONVEYOR_OBSIDIAN", "0")
    res = conveyor.run_obsidian_export(
        runner=lambda *a, **kw: pytest.fail("must not run when disabled"))
    assert res["ran"] is False
