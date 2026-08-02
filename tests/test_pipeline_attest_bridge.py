"""Tests for scripts/pipeline_attest_bridge.py (print-only formalize→verify plan)."""
from __future__ import annotations

import json
import os
import sys
import textwrap

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import pipeline_attest_bridge as bridge  # noqa: E402


@pytest.fixture()
def sample_lean(tmp_path):
    p = tmp_path / "SampleMod.lean"
    p.write_text(
        textwrap.dedent(
            """\
            import Mathlib
            namespace Brockian.SampleMod

            def helper : Nat := 1

            theorem foo : True := trivial
            lemma bar : True := trivial

            -- theorem commented_out : False := sorry

            end Brockian.SampleMod
            """
        ),
        encoding="utf-8",
    )
    return str(p)


def test_discover_namespace_and_names(sample_lean):
    assert bridge.discover_namespace(sample_lean) == "Brockian.SampleMod"
    names = bridge.discover_names(sample_lean)
    assert "foo" in names
    assert "bar" in names
    assert "helper" in names
    assert "commented_out" not in names


def test_build_plan_prints_attest_and_registry(sample_lean):
    plan = bridge.build_plan(
        lean_path=sample_lean,
        names=[],
        namespace="Brockian.SampleMod",
        env="lean-4.32.0",
        refute=None,
        pipeline_id=None,
        include_settle=True,
    )
    cmds = {c["step"]: c["cmd"] for c in plan["commands"]}
    assert "no_theater_lint.py" in cmds["lint"]
    assert cmds["attest"].startswith("python3 scripts/attest.py")
    assert "Brockian.SampleMod" in cmds["attest"]
    assert " foo " in f" {cmds['attest']} " or cmds["attest"].endswith(" foo") or " foo" in cmds["attest"]
    assert "bar" in cmds["attest"]
    assert cmds["registry"] == "python3 scripts/gen_registry.py"
    assert "settle.py" in cmds["settle"]
    assert plan["attestation_out"].endswith("SampleMod.json")


def test_explicit_names_override_discovery(sample_lean):
    plan = bridge.build_plan(
        lean_path=sample_lean,
        names=["foo"],
        namespace="Brockian.SampleMod",
        env="lean-4.28.0",
        refute="aristotle/neg/target.lean",
        pipeline_id="distill-etp-stage2",
        include_settle=True,
    )
    assert plan["names"] == ["foo"]
    attest = plan["commands"][1]["cmd"]
    assert "foo" in attest
    assert "bar" not in attest
    assert "--env lean-4.28.0" in attest
    settle = next(c for c in plan["commands"] if c["step"] == "settle")["cmd"]
    assert "--refute aristotle/neg/target.lean" in settle
    assert any(c["step"] == "pipeline_attempt_proved" for c in plan["pipeline_commands"])
    assert any(c["step"] == "pipeline_attempt_refuted" for c in plan["pipeline_commands"])


def test_main_json_and_text(sample_lean, capsys):
    rc = bridge.main([sample_lean, "--json", "--no-settle"])
    assert rc == 0
    out = capsys.readouterr().out
    data = json.loads(out)
    assert data["namespace"] == "Brockian.SampleMod"
    assert data["n_names"] >= 2
    assert all(c["step"] != "settle" for c in data["commands"])

    rc = bridge.main([sample_lean, "foo"])
    assert rc == 0
    text = capsys.readouterr().out
    assert "formalize→verify plan" in text
    assert "scripts/attest.py" in text
    assert "scripts/gen_registry.py" in text


def test_missing_file_exits():
    rc = bridge.main(["Brockian/DoesNotExistXYZ.lean"])
    assert rc == 2
