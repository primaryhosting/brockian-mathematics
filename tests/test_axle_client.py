"""Live tests for the AXLE client. Require AXLE_API_KEY and network.

Run: python3 -m pytest tests/test_axle_client.py -v
"""
import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import axle_client  # noqa: E402

pytestmark = pytest.mark.skipif(
    not os.environ.get("AXLE_API_KEY"), reason="AXLE_API_KEY not set"
)

ENV = os.environ.get("AXLE_ENV", "lean-4.32.2")


def test_check_true_theorem():
    r = axle_client.check("import Mathlib\ntheorem t : 1 + 1 = 2 := by decide", env=ENV)
    assert r.verified is True
    assert r.errors == []


def test_check_false_theorem_not_verified():
    # 1 + 1 = 3 does not hold; `decide` fails → not verified.
    r = axle_client.check("import Mathlib\ntheorem t : 1 + 1 = 3 := by decide", env=ENV)
    assert r.verified is False


def test_check_sorry_not_verified():
    r = axle_client.check("import Mathlib\ntheorem t : True := by sorry", env=ENV)
    assert r.verified is False
