"""Tests for engine.verify — the shared AXLE verification core.

These pin the contracts every caller depends on: the canonical normalize/content_hash,
fully-qualified #print-axioms targeting, and the trusted/flagged/unknown verdict from
AXLE's messages. AXLE is mocked; no network."""
from engine import verify


# --------------------------------------------------------- normalize / content_hash

def test_normalize_hoists_and_dedupes_imports():
    src = "import Mathlib\nnamespace N\nimport Mathlib\ntheorem t : True := trivial\nend N\n"
    out = verify.normalize(src)
    assert out.splitlines()[0] == "import Mathlib"
    assert out.count("import Mathlib") == 1  # deduped
    assert "theorem t" in out


def test_content_hash_stable_and_normalization_invariant():
    # identical body; imports differ only in placement (mid-file vs hoisted) + a dup.
    # normalize hoists+dedupes imports, so the two hash identically.
    a = "-- header\nimport Mathlib\ntheorem t : True := trivial\n"
    b = "import Mathlib\n-- header\ntheorem t : True := trivial\nimport Mathlib\n"
    assert verify.content_hash(a) == verify.content_hash(b)
    assert len(verify.content_hash(a)) == 16


# ------------------------------------------------------- namespace qualification

def test_qualified_decls_prefixes_namespace_and_ignores_sections():
    text = ("theorem top : True := trivial\n"
            "namespace Brockian.Foo\n"
            "section S\n"
            "theorem inner : True := trivial\n"
            "end S\n"
            "lemma outer : True := trivial\n"
            "end Brockian.Foo\n")
    assert verify.qualified_decls(text) == [
        "top", "Brockian.Foo.inner", "Brockian.Foo.outer"]


def test_qualified_decls_handles_attributes_and_modifiers():
    text = "namespace N\n@[simp]\nprivate theorem p : True := trivial\nend N\n"
    assert verify.qualified_decls(text) == ["N.p"]


# ---------------------------------------------------------------- axiom parsing

def test_parse_axioms_formats():
    assert verify.parse_axioms(
        ["info: 'a' does not depend on any axioms\n"]) == set()
    assert verify.parse_axioms(
        ["info: 'b' depends on axioms: [propext, Classical.choice, Quot.sound]\n"]
    ) == {"propext", "Classical.choice", "Quot.sound"}
    assert verify.parse_axioms(["info: 'h' depends on axioms: [sorryAx]\n"]) == {"sorryAx"}


def test_axioms_in_line_per_line_parser():
    # attest.py's per-decl attribution relies on this: order-preserving list, or None
    assert verify.axioms_in_line("info: 'a' does not depend on any axioms\n") == []
    assert verify.axioms_in_line(
        "info: 'b' depends on axioms: [propext, Quot.sound]\n") == ["propext", "Quot.sound"]
    assert verify.axioms_in_line(
        "info: 'b' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
    ) == ["propext", "Classical.choice", "Quot.sound"]
    assert verify.axioms_in_line("some unrelated info line\n") is None


# ---------------------------------------------------------- axiom_audit verdicts

def _mock(monkeypatch, resp):
    monkeypatch.setattr(verify.ax, "_post", lambda *a, **k: resp)


def test_axiom_audit_trusted_on_kernel_clean(monkeypatch):
    _mock(monkeypatch, {"okay": True, "lean_messages": {"errors": [], "warnings": [],
          "infos": ["info: 'N.t' depends on axioms: [propext, Classical.choice, Quot.sound]\n"]}})
    r = verify.axiom_audit("import Mathlib\nnamespace N\ntheorem t : True := trivial\nend N\n")
    assert r["trusted"] is True and r["detail"] is None
    assert r["axioms"] == ["Classical.choice", "Quot.sound", "propext"]
    assert r["environment"] == verify.DEFAULT_ENV


def test_axiom_audit_flags_extra_axiom(monkeypatch):
    _mock(monkeypatch, {"okay": True, "lean_messages": {"errors": [], "warnings": [],
          "infos": ["info: 't' depends on axioms: [propext, Nat.badAxiom]\n"]}})
    r = verify.axiom_audit("theorem t : True := trivial\n")
    assert r["trusted"] is False and "Nat.badAxiom" in r["extra_axioms"]


def test_axiom_audit_flags_sorry(monkeypatch):
    _mock(monkeypatch, {"okay": True, "lean_messages": {
        "errors": [], "warnings": ["warning: declaration uses `sorry`\n"],
        "infos": ["info: 't' depends on axioms: [sorryAx]\n"]}})
    assert verify.axiom_audit("theorem t : True := by sorry\n")["trusted"] is False


def test_axiom_audit_unknown_on_compile_error(monkeypatch):
    _mock(monkeypatch, {"okay": False, "lean_messages": {"errors": ["error: boom\n"],
          "warnings": [], "infos": []}})
    r = verify.axiom_audit("theorem t : True := trivial\n")
    assert r["trusted"] is None and "compile error" in r["detail"]


def test_axiom_audit_unknown_when_no_theorem(monkeypatch):
    _mock(monkeypatch, {"okay": True, "lean_messages": {"errors": [], "warnings": [], "infos": []}})
    r = verify.axiom_audit("import Mathlib\nset_option maxHeartbeats 400\n")
    assert r["trusted"] is None and "no theorem" in r["detail"]


def test_axiom_audit_honors_explicit_probe_targets_and_preamble(monkeypatch):
    seen = {}

    def cap(tool, payload, timeout=120):
        seen["content"] = payload["content"]
        return {"okay": True, "lean_messages": {"errors": [], "warnings": [],
                "infos": ["info: 'Foo.bar' does not depend on any axioms\n"]}}
    monkeypatch.setattr(verify.ax, "_post", cap)
    # attest.py-style call: explicit names + an `open` preamble, content unchanged
    r = verify.axiom_audit("import Mathlib\ntheorem bar : True := trivial\n",
                           probe_targets=["bar"], preamble="open Foo")
    assert r["trusted"] is True
    assert "open Foo" in seen["content"]
    assert "#print axioms bar" in seen["content"]
