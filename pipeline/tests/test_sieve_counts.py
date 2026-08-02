"""Golden parity tests for pipeline/artifacts/cs/sieve_counts.py."""
from __future__ import annotations

import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO))

from pipeline.artifacts.cs import sieve_counts as sc  # noqa: E402


def test_pair_q3_q5_golden():
    assert sc.pair_count(3, 1) == 1
    assert sc.pair_count(5, 1) == 3
    assert sc.pair_count(3, 0) == 2
    assert sc.pair_count(5, 0) == 4


def test_crt_product_three_five():
    assert sc.crt_pair_product(3, 1, 5, 1) == 3


def test_ktuple_lean_decide_cases():
    assert sc.ktuple_count(3, [0, 1]) == 1
    assert sc.ktuple_count(5, [0, 1, 3]) == 2


def test_dichotomy_closed_form():
    for q in range(1, 16):
        for g in range(q):
            assert sc.pair_count(q, g) == sc.pair_count_closed_form(q, g)


def test_run_checks_all_pass():
    n_ok, n_fail, rows = sc.run_checks(verbose=False)
    assert n_fail == 0, rows
    assert n_ok == len(sc.GOLDEN)


def test_main_check_exit_zero():
    assert sc.main(["--check", "--quiet"]) == 0
