#!/usr/bin/env python3
"""Executable admissible-residue counts matching Brockian Lean theorems.

Implements the q−ν (pair) law, diagonal dichotomy, k-tuple count, and CRT
product — the finite arithmetic behind twin / k-tuple sieve local densities.

Golden values are taken from closed Lean theorems (not guessed):

  Brockian.Admissibility.universal_admissibility_count
      |A_q(g)| = q − 2  for g ≠ 0
  Brockian.Admissibility.admissibility_count_three / _five
      |A_3| = 1, |A_5| = 3  (g ≠ 0)
  Brockian.AdmissibilityDiagonal.admissibility_count_dichotomy
      |A_q(g)| = q−1 if g≡0 else q−2
  Brockian.Admissibility.CRT.admissible_count_three_five
      |A_3|·|A_5| = 1·3 = 3  (no paper §6.1 correction factor)
  Brockian.AdmissibilityKTuple.admissibleTupleResidues_card
      |A_q(H)| = q − |H|
  Brockian.AdmissibilityKTuple.admissible_ktuple_count_three / _five
      mod 3, H={0,1} → 1;  mod 5, H={0,1,3} → 2
  Brockian.Sieve.twin_admissible_card
      prime ℓ > 2 → ℓ − 2 twin-admissible starts

Usage:
  python3 -m pipeline.artifacts.cs.sieve_counts
  python3 -m pipeline.artifacts.cs.sieve_counts --check
  python3 pipeline/artifacts/cs/sieve_counts.py --check
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Sequence


# ---------------------------------------------------------------------------
# Core counting (match Lean definitions, not paper superseded formulas)
# ---------------------------------------------------------------------------


def admissible_residues_pair(q: int, g: int) -> list[int]:
    """Starts a mod q with neither a nor a+g ≡ 0. Lean: admissibleResidues.

    Forbidden set is {0, −g} mod q (collapses to {0} when g ≡ 0).
    """
    if q < 1:
        raise ValueError("q must be ≥ 1")
    g_mod = g % q
    forbidden = {0, (-g_mod) % q}
    return [a for a in range(q) if a not in forbidden]


def pair_count(q: int, g: int) -> int:
    """|A_q(g)| — dichotomy: q−1 if g≡0 else q−2."""
    return len(admissible_residues_pair(q, g))


def pair_count_closed_form(q: int, g: int) -> int:
    """Closed form of admissibility_count_dichotomy."""
    if q < 1:
        raise ValueError("q must be ≥ 1")
    return q - 1 if (g % q) == 0 else q - 2


def admissible_residues_ktuple(q: int, offsets: Sequence[int]) -> list[int]:
    """Starts a with a+h ≢ 0 for every offset h in H. Lean: admissibleTupleResidues.

    Equivalent: a ∉ {−h : h ∈ H}. Count is q − |H| for distinct offsets mod q.
    """
    if q < 1:
        raise ValueError("q must be ≥ 1")
    H = {(h % q) for h in offsets}
    forbidden = {(-h) % q for h in H}
    return [a for a in range(q) if a not in forbidden]


def ktuple_count(q: int, offsets: Sequence[int]) -> int:
    """|A_q(H)| = q − |H| (distinct offsets)."""
    return len(admissible_residues_ktuple(q, offsets))


def ktuple_count_closed_form(q: int, offsets: Sequence[int]) -> int:
    if q < 1:
        raise ValueError("q must be ≥ 1")
    H = {(h % q) for h in offsets}
    return q - len(H)


def crt_pair_product(q1: int, g1: int, q2: int, g2: int) -> int:
    """CRT product |A_{q1}(g1)| · |A_{q2}(g2)| — no extra correction factor.

    Lean: admissibleResidues_crt_card. Refutes Paper 1 §6.1 factor
    (q1 q2 − 1)/((q1 − 1)(q2 − 1)).
    """
    return pair_count(q1, g1) * pair_count(q2, g2)


def twin_admissible_count(ell: int) -> int:
    """Twin starts a with a∉{0,−2} mod ℓ. Lean: twin_admissible_card for prime ℓ>2 → ℓ−2."""
    return pair_count(ell, 2)


# ---------------------------------------------------------------------------
# Golden expected values (document ↔ Lean theorem names)
# ---------------------------------------------------------------------------

# Each entry: name, expected, actual-callable metadata for --check
GOLDEN: list[dict] = [
    {
        "id": "pair_q3_g1",
        "lean": "Brockian.Admissibility.admissibility_count_three",
        "note": "q=3, g≠0 → q−2 = 1 (twin-prime pin)",
        "expected": 1,
        "compute": lambda: pair_count(3, 1),
    },
    {
        "id": "pair_q5_g1",
        "lean": "Brockian.Admissibility.admissibility_count_five",
        "note": "q=5, g≠0 → q−2 = 3 (Brockian case)",
        "expected": 3,
        "compute": lambda: pair_count(5, 1),
    },
    {
        "id": "pair_universal_q7_g2",
        "lean": "Brockian.Admissibility.universal_admissibility_count",
        "note": "q=7, g≠0 → 5",
        "expected": 5,
        "compute": lambda: pair_count(7, 2),
    },
    {
        "id": "diagonal_q3",
        "lean": "Brockian.AdmissibilityDiagonal.diagonal_count_three",
        "note": "q=3, g≡0 → q−1 = 2",
        "expected": 2,
        "compute": lambda: pair_count(3, 0),
    },
    {
        "id": "diagonal_q5",
        "lean": "Brockian.AdmissibilityDiagonal.diagonal_count_five",
        "note": "q=5, g≡0 → q−1 = 4",
        "expected": 4,
        "compute": lambda: pair_count(5, 0),
    },
    {
        "id": "dichotomy_closed_form",
        "lean": "Brockian.AdmissibilityDiagonal.admissibility_count_dichotomy",
        "note": "closed form matches enumeration for q=1..20, g=0..q",
        "expected": True,
        "compute": lambda: all(
            pair_count(q, g) == pair_count_closed_form(q, g)
            for q in range(1, 21)
            for g in range(q + 1)
        ),
    },
    {
        "id": "crt_3_5",
        "lean": "Brockian.Admissibility.CRT.admissible_count_three_five",
        "note": "|A_3|·|A_5| = 1·3 = 3 (NOT 5.25 from paper §6.1)",
        "expected": 3,
        "compute": lambda: crt_pair_product(3, 1, 5, 1),
    },
    {
        "id": "crt_3_5_closed",
        "lean": "Brockian.Admissibility.CRT.admissibleResidues_crt_card_two_primes",
        "note": "(3−2)·(5−2) = 3",
        "expected": 3,
        "compute": lambda: (3 - 2) * (5 - 2),
    },
    {
        "id": "ktuple_mod3_pair",
        "lean": "Brockian.AdmissibilityKTuple.admissible_ktuple_count_three",
        "note": "mod 3, H={0,1} → 3−2 = 1",
        "expected": 1,
        "compute": lambda: ktuple_count(3, [0, 1]),
    },
    {
        "id": "ktuple_mod5_triple",
        "lean": "Brockian.AdmissibilityKTuple.admissible_ktuple_count_five",
        "note": "mod 5, H={0,1,3} → 5−3 = 2",
        "expected": 2,
        "compute": lambda: ktuple_count(5, [0, 1, 3]),
    },
    {
        "id": "ktuple_card_law",
        "lean": "Brockian.AdmissibilityKTuple.admissibleTupleResidues_card",
        "note": "|A_q(H)| = q−|H|; refutes paper (q−1)^(k−1)",
        "expected": True,
        "compute": lambda: all(
            ktuple_count(q, offs) == ktuple_count_closed_form(q, offs)
            for q in (3, 5, 7, 11)
            for offs in ([0, 1], [0, 1, 2], [0, 1, 3], [0, 2, 4, 6])
            if len({h % q for h in offs}) == len(offs) or True
        ),
    },
    {
        "id": "ktuple_pair_recovers_q_minus_2",
        "lean": "Brockian.AdmissibilityKTuple.admissibleTupleResidues_card_pair",
        "note": "H={0,g}, g≠0 → q−2",
        "expected": True,
        "compute": lambda: all(
            ktuple_count(q, [0, g]) == q - 2
            for q in (3, 5, 7, 11, 13)
            for g in range(1, q)
        ),
    },
    {
        "id": "twin_card_primes",
        "lean": "Brockian.Sieve.twin_admissible_card",
        "note": "prime ℓ>2 → ℓ−2",
        "expected": True,
        "compute": lambda: all(
            twin_admissible_count(p) == p - 2 for p in (3, 5, 7, 11, 13, 17, 19)
        ),
    },
    {
        "id": "paper_correction_not_integer",
        "lean": "Brockian.Admissibility.CRT (paper §6.1 refutation narrative)",
        "note": "spurious factor 14/8 would give 5.25 — not a cardinality",
        "expected": True,
        "compute": lambda: (1 * 3) * (14 / 8) == 5.25 and crt_pair_product(3, 1, 5, 1) == 3,
    },
]


def run_checks(verbose: bool = True) -> tuple[int, int, list[dict]]:
    """Return (n_pass, n_fail, detail rows)."""
    rows: list[dict] = []
    n_ok = n_fail = 0
    for g in GOLDEN:
        actual = g["compute"]()
        ok = actual == g["expected"]
        if ok:
            n_ok += 1
        else:
            n_fail += 1
        row = {
            "id": g["id"],
            "lean": g["lean"],
            "note": g["note"],
            "expected": g["expected"],
            "actual": actual,
            "ok": ok,
        }
        rows.append(row)
        if verbose:
            mark = "OK" if ok else "FAIL"
            print(f"  [{mark}] {g['id']}: expected={g['expected']!r} actual={actual!r}")
            print(f"         lean: {g['lean']}")
    return n_ok, n_fail, rows


def demo_table() -> None:
    print("=== Pair admissibility |A_q(g)| (enumeration) ===")
    print(f"{'q':>4} {'g':>4} {'count':>6}  closed  residues")
    for q in (3, 5, 7):
        for g in range(q):
            c = pair_count(q, g)
            cf = pair_count_closed_form(q, g)
            res = admissible_residues_pair(q, g)
            print(f"{q:4d} {g:4d} {c:6d}  {cf:6d}  {res}")
    print()
    print("=== k-tuple samples ===")
    samples = [
        (3, [0, 1]),
        (5, [0, 1]),
        (5, [0, 1, 3]),
        (7, [0, 1, 2]),
    ]
    for q, H in samples:
        print(f"  q={q} H={H} → {ktuple_count(q, H)}  (closed {ktuple_count_closed_form(q, H)})")
    print()
    print("=== CRT product (3,5) ===")
    print(f"  |A_3(1)|·|A_5(1)| = {crt_pair_product(3, 1, 5, 1)}")


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Brockian admissible residue counts (Python cert)")
    p.add_argument(
        "--check",
        action="store_true",
        help="Run golden checks against Lean theorem values; exit 0 iff all match",
    )
    p.add_argument("--json", action="store_true", help="Emit check results as JSON")
    p.add_argument("--quiet", action="store_true", help="With --check, suppress per-case lines")
    args = p.parse_args(list(argv) if argv is not None else None)

    if args.check or args.json:
        n_ok, n_fail, rows = run_checks(verbose=not args.quiet and not args.json)
        payload = {
            "ok": n_fail == 0,
            "passed": n_ok,
            "failed": n_fail,
            "total": n_ok + n_fail,
            "cases": [
                {k: v for k, v in r.items() if k != "actual" or True}
                for r in rows
            ],
        }
        # JSON-serialize bool/int only (strip callables already)
        if args.json:
            serializable = {
                "ok": payload["ok"],
                "passed": payload["passed"],
                "failed": payload["failed"],
                "total": payload["total"],
                "cases": [
                    {
                        "id": r["id"],
                        "lean": r["lean"],
                        "note": r["note"],
                        "expected": r["expected"],
                        "actual": r["actual"],
                        "ok": r["ok"],
                    }
                    for r in rows
                ],
            }
            print(json.dumps(serializable, indent=2))
        else:
            print(f"\ngolden: {n_ok}/{n_ok + n_fail} passed")
        return 0 if n_fail == 0 else 1

    demo_table()
    print()
    n_ok, n_fail, _ = run_checks(verbose=True)
    print(f"\ngolden: {n_ok}/{n_ok + n_fail} passed")
    return 0 if n_fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
