"""Tests for engine.audit — the unified honesty gate.

Pins the aggregation contract (any failing surface fails --strict; --strict is required to
fail) and the claimed-module parsing that feeds the no-theater closed set."""
import sys

from engine import audit


def test_claimed_modules_are_short_names_from_brockian_lean():
    mods = audit.claimed_modules()
    assert isinstance(mods, set) and len(mods) > 0
    assert all("." not in m and m for m in mods)  # short names, non-empty


def test_main_fails_strict_when_any_surface_fails(monkeypatch):
    monkeypatch.setattr(audit, "run",
                        lambda strict=True: [("registry-consistency", True, ""),
                                             ("overclaim-firewall", False, "boom")])
    monkeypatch.setattr(sys, "argv", ["engine.audit", "--strict"])
    assert audit.main() == 1


def test_main_passes_when_all_surfaces_ok(monkeypatch):
    monkeypatch.setattr(audit, "run",
                        lambda strict=True: [("a", True, ""), ("b", True, "")])
    monkeypatch.setattr(sys, "argv", ["engine.audit", "--strict"])
    assert audit.main() == 0


def test_main_nonstrict_never_fails(monkeypatch):
    # without --strict, a failing surface is reported but does not gate (exit 0)
    monkeypatch.setattr(audit, "run", lambda strict=True: [("a", False, "x")])
    monkeypatch.setattr(sys, "argv", ["engine.audit"])
    assert audit.main() == 0


def test_run_reports_three_surfaces(monkeypatch):
    calls = []

    def fake_subrun(cmd, cwd=None, capture_output=True, text=True):
        calls.append(cmd)
        class R:
            returncode = 0
            stdout = ""
            stderr = ""
        return R()
    monkeypatch.setattr(audit.subprocess, "run", fake_subrun)
    results = audit.run(strict=True)
    names = [n for n, _, _ in results]
    assert names == ["registry-consistency", "overclaim-firewall", "no-theater-lint"]
    assert all(ok for _, ok, _ in results)
    # the registry-consistency surface was invoked with --strict
    assert any(any("audit_registry_consistency.py" in a for a in c) and "--strict" in c
               for c in calls)
