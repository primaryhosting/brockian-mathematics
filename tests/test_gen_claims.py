"""Unit tests for observatory claim generation (no network)."""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import gen_claims  # noqa: E402


def test_resolve_proved_claim():
    by_name = {
        "Brockian.GoldbachComb.gCount_eq": {
            "name": "Brockian.GoldbachComb.gCount_eq",
            "kind": "theorem",
            "module": "Brockian.GoldbachComb",
            "register": "PROVED",
            "source": {"file": "Brockian/GoldbachComb.lean"},
            "verification": {
                "axioms_ok": True,
                "axle": {"verdict": "verified", "environment": "lean-4.32.0"},
            },
        }
    }
    claim = {
        "id": "GC-1",
        "title": "Local count",
        "book": "Vol III",
        "lean": ["Brockian.GoldbachComb.gCount_eq"],
        "notes": "",
    }
    out = gen_claims.resolve_claim(claim, by_name)
    assert out["derived_register"] == "PROVED"
    assert out["book_badge"] == "V3-LEAN-RUN"
    assert out["proved_count"] == 1
    assert out["missing_lean"] == []


def test_resolve_not_claimed():
    out = gen_claims.resolve_claim(
        {"id": "OPEN-RH", "title": "RH", "lean": [], "badge_force": "not_claimed", "notes": ""},
        {},
    )
    assert out["book_badge"] == "NOT-CLAIMED"
    assert out["status"] == "not_claimed"


def test_resolve_conditional_beats_proved_scaffolding():
    by_name = {
        "Brockian.RiemannScaffold.RH_of_BrockianSystem": {
            "name": "Brockian.RiemannScaffold.RH_of_BrockianSystem",
            "kind": "theorem",
            "module": "Brockian.RiemannScaffold",
            "register": "CONDITIONAL",
            "source": {"file": "Brockian/RiemannScaffold.lean"},
            "verification": {"axioms_ok": True, "axle": {"verdict": "verified"}},
        },
        "Brockian.RiemannScaffold.riemannXi": {
            "name": "Brockian.RiemannScaffold.riemannXi",
            "kind": "def",
            "module": "Brockian.RiemannScaffold",
            "register": "DEFINITION",
            "source": {"file": "Brockian/RiemannScaffold.lean"},
            "verification": {"axioms_ok": True, "axle": {"verdict": "verified"}},
        },
    }
    out = gen_claims.resolve_claim(
        {
            "id": "RH-BROCKIAN-SYSTEM",
            "title": "RH schema",
            "lean": [
                "Brockian.RiemannScaffold.RH_of_BrockianSystem",
                "Brockian.RiemannScaffold.riemannXi",
            ],
            "notes": "",
        },
        by_name,
    )
    assert out["derived_register"] == "CONDITIONAL"
    assert out["book_badge"] == "CONDITIONAL"


def test_build_claims_doc_summary():
    reg = {
        "summary": {"PROVED": 1, "DEFINITION": 0, "CONJECTURE": 0, "CONDITIONAL": 0},
        "theorems": [
            {
                "name": "Brockian.Core.fib_five_dvd",
                "kind": "theorem",
                "module": "Brockian.Core",
                "register": "PROVED",
                "source": {"file": "Brockian/Core.lean"},
                "verification": {"axioms_ok": True, "axle": {"verdict": "verified"}},
            }
        ],
    }
    cmap = {
        "version": 1,
        "program": "Test",
        "charter": "test charter",
        "claims": [
            {
                "id": "FIB-FIVE",
                "title": "Fib five",
                "lean": ["Brockian.Core.fib_five_dvd"],
                "notes": "",
            }
        ],
    }
    doc = gen_claims.build_claims_doc(reg, cmap)
    assert doc["summary"]["claims"] == 1
    assert doc["summary"]["by_status"]["proved"] == 1
    assert len(doc["all_declarations"]) == 1
