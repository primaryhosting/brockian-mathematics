"""Tests for engine.register.derive — the single derived-register gate.

Covers every precedence branch, and pins the PROVED gate (the load-bearing honesty rule)
so it cannot silently loosen when gen_registry / the validators delegate to it."""
import pytest

from engine.register import DeclFacts, Flags, derive


def _thm(**kw):
    base = dict(name="t", kind="theorem", axioms=["propext"], axle_verified=True)
    base.update(kw)
    return DeclFacts(**base)


def test_conjecture_and_definition_kinds():
    assert derive(DeclFacts(name="c", kind="conjecture")) == "CONJECTURE"
    assert derive(DeclFacts(name="d", kind="def")) == "DEFINITION"
    assert derive(DeclFacts(name="a", kind="abbrev")) == "DEFINITION"
    assert derive(DeclFacts(name="x", kind="instance")) == "CONJECTURE"  # non-thm/lemma


def test_conditional_beats_proved():
    assert derive(_thm(conditional_rung="literature")) == "CONDITIONAL"


def test_invalid_rung_raises():
    with pytest.raises(ValueError):
        derive(_thm(conditional_rung="bogus"))


def test_native_decide_is_computation():
    assert derive(_thm(flags=Flags(native_decide=True))) == "COMPUTATION"


def test_proved_requires_all_legs():
    assert derive(_thm()) == "PROVED"
    # each leg failing drops PROVED to UNVERIFIED
    assert derive(_thm(axle_verified=None)) == "UNVERIFIED"
    assert derive(_thm(axle_verified=False)) == "UNVERIFIED"
    assert derive(_thm(flags=Flags(sorry=True))) == "UNVERIFIED"
    assert derive(_thm(flags=Flags(exact_search=True))) == "UNVERIFIED"
    assert derive(_thm(axioms=["propext", "sorryAx"])) == "UNVERIFIED"
    assert derive(_thm(axioms=["propext", "Nat.badAxiom"])) == "UNVERIFIED"
    assert derive(_thm(axioms_ok=False)) == "UNVERIFIED"
    assert derive(_thm(verification_quarantine=True)) == "UNVERIFIED"
    assert derive(_thm(verification_quarantine=True,
                       conditional_rung="literature")) == "UNVERIFIED"
    assert derive(_thm(verification_quarantine=True,
                       flags=Flags(native_decide=True))) == "UNVERIFIED"


def test_lemma_is_theorem_grade():
    assert derive(_thm(kind="lemma")) == "PROVED"


def test_all_three_kernel_axioms_are_allowed():
    assert derive(_thm(axioms=["propext", "Classical.choice", "Quot.sound"])) == "PROVED"


def test_parity_with_gen_registry_derive_register():
    """engine.register.derive must match the legacy scripts/gen_registry.derive_register
    it will replace, across a matrix of fact combinations (behavior-preservation gate)."""
    import importlib.util
    import pathlib
    import sys
    p = pathlib.Path(__file__).resolve().parent.parent / "scripts" / "gen_registry.py"
    spec = importlib.util.spec_from_file_location("gen_registry_legacy", p)
    legacy = importlib.util.module_from_spec(spec)
    sys.modules["gen_registry_legacy"] = legacy  # dataclass field resolution needs this
    spec.loader.exec_module(legacy)

    cases = []
    for kind in ("theorem", "lemma", "def", "abbrev", "conjecture", "instance"):
        for axle in (True, False, None):
            for ax in (["propext"], ["propext", "sorryAx"], ["Classical.choice"], []):
                for fl in (Flags(), Flags(native_decide=True), Flags(sorry=True),
                           Flags(exact_search=True)):
                    for rung in (None, "classical", "open"):
                        cases.append((kind, axle, ax, fl, rung))
    for kind, axle, ax, fl, rung in cases:
        mine = DeclFacts(name="n", kind=kind, axioms=ax, flags=fl,
                         axle_verified=axle, conditional_rung=rung)
        theirs = legacy.DeclFacts(
            name="n", kind=kind, axioms=ax,
            flags=legacy.Flags(native_decide=fl.native_decide, sorry=fl.sorry,
                               exact_search=fl.exact_search),
            axle_verified=axle, conditional_rung=rung)
        assert derive(mine) == legacy.derive_register(theirs), (kind, axle, ax, fl, rung)
