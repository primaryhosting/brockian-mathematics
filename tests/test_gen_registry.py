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
