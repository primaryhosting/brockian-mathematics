import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma eq_pow_mul_pow_of_primeFactors_eq_pair {n p q : ℕ} (hn : n ≠ 0) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  trans ∏ x ∈ n.primeFactors, x ^ n.factorization x
  · rfl
  · rw [hS]
    simp [Finset.prod_pair hpq]

/-- An odd prime factor is at least `3`. -/
