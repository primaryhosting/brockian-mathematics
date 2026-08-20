import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma deficient_of_sum_divisors_lt {n : ℕ}
    (h : ∑ d ∈ n.divisors, d < 2 * n) : Nat.Deficient n := by
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, two_mul] at h
  exact Nat.lt_of_add_lt_add_right h

/-- A number with prime factors exactly `{p, q}` factors as `p ^ a * q ^ b`. -/
