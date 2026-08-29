import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma rad_le_two_mul_odd_part (x : ℕ) :
    rad x ≤ 2 * ∏ p ∈ x.primeFactors \ {2}, p := by
  classical
  by_cases h2 : 2 ∈ x.primeFactors
  · have : rad x = 2 * ∏ p ∈ x.primeFactors.erase 2, p := (Finset.mul_prod_erase _ _ h2).symm
    rw [this, Finset.sdiff_singleton_eq_erase]
  · have hs : x.primeFactors \ {2} = x.primeFactors := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem h2]
    rw [hs]
    exact Nat.le_mul_of_pos_left _ (by norm_num)

/-- If `2 ^ k ∣ x` then `2 ^ k * rad x ≤ 2 * x`. -/
