"""Tests for the cloud axiom audit (aristotle/axle_axiom_audit.py).

The audit is the soundness leg that promotes a proof to registry PROVED now that
local Lean cannot run on this box. These tests pin the two things that must not
regress: fully-qualified `#print axioms` targeting (a bare name fails to resolve at
end-of-file), and the trusted/flagged/unknown verdict derived from AXLE's messages."""
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "aristotle"))
import axle_axiom_audit as aud  # noqa: E402


# ------------------------------------------------------- namespace qualification

def test_qualified_decls_prefixes_namespace():
    text = ("import Mathlib\n"
            "namespace Brockian.Foo\n"
            "theorem bar : True := trivial\n"
            "lemma baz : True := trivial\n"
            "end Brockian.Foo\n")
    assert aud.qualified_decls(text) == [
        "Brockian.Foo.bar", "Brockian.Foo.baz"]


def test_qualified_decls_top_level_and_sections():
    # a `section` scope does NOT contribute to the name path; `namespace` does
    text = ("theorem top : True := trivial\n"
            "namespace N\n"
            "section S\n"
            "theorem inner : True := trivial\n"
            "end S\n"
            "end N\n")
    assert aud.qualified_decls(text) == ["top", "N.inner"]


def test_qualified_decls_handles_attributes_and_modifiers():
    text = ("namespace N\n"
            "@[simp]\n"
            "private theorem p : True := trivial\n"
            "end N\n")
    assert aud.qualified_decls(text) == ["N.p"]


# ------------------------------------------------------------- axiom parsing

def test_parse_axioms_clean_and_listed_and_sorry():
    infos = [
        "-:5:0-5:6: info: 'a' does not depend on any axioms\n",
        "-:6:0-6:6: info: 'b' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
    ]
    assert aud.parse_axioms(infos) == {"propext", "Classical.choice", "Quot.sound"}
    assert aud.parse_axioms(
        ["-:9:0: info: 'h' depends on axioms: [sorryAx]\n"]) == {"sorryAx"}
    assert aud.parse_axioms([]) == set()


# ------------------------------------------------------------- verdict logic

def _mock_post(monkeypatch, resp):
    monkeypatch.setattr(aud.ax, "_post", lambda *a, **k: resp)


def test_audit_one_trusted_on_kernel_clean(monkeypatch):
    _mock_post(monkeypatch, {
        "okay": True,
        "lean_messages": {"errors": [], "warnings": [], "infos": [
            "info: 'N.t' depends on axioms: [propext, Classical.choice, Quot.sound]\n"]},
    })
    trusted, axioms, detail = aud.audit_one(
        "import Mathlib\nnamespace N\ntheorem t : True := trivial\nend N\n")
    assert trusted is True and detail is None
    assert axioms == ["Classical.choice", "Quot.sound", "propext"]


def test_audit_one_flags_extra_axiom(monkeypatch):
    _mock_post(monkeypatch, {
        "okay": True,
        "lean_messages": {"errors": [], "warnings": [], "infos": [
            "info: 't' depends on axioms: [propext, Nat.someUnsoundAxiom]\n"]},
    })
    trusted, axioms, detail = aud.audit_one("theorem t : True := trivial\n")
    assert trusted is False
    assert "Nat.someUnsoundAxiom" in axioms


def test_audit_one_flags_sorry_ax(monkeypatch):
    _mock_post(monkeypatch, {
        "okay": True,
        "lean_messages": {"errors": [],
                          "warnings": ["warning: declaration uses `sorry`\n"],
                          "infos": ["info: 't' depends on axioms: [sorryAx]\n"]},
    })
    trusted, _, _ = aud.audit_one("theorem t : True := by sorry\n")
    assert trusted is False


def test_audit_one_unknown_on_compile_error(monkeypatch):
    _mock_post(monkeypatch, {
        "okay": False,
        "lean_messages": {"errors": ["error: boom\n"], "warnings": [], "infos": []},
    })
    trusted, _, detail = aud.audit_one("theorem t : True := trivial\n")
    assert trusted is None and "compile error" in detail


def test_audit_one_unknown_when_no_theorem(monkeypatch):
    # an empty stub compiles (AXLE says verified) but has nothing to trust
    _mock_post(monkeypatch, {"okay": True,
                             "lean_messages": {"errors": [], "warnings": [], "infos": []}})
    trusted, _, detail = aud.audit_one("import Mathlib\nset_option maxHeartbeats 400\n")
    assert trusted is None and "no theorem" in detail
