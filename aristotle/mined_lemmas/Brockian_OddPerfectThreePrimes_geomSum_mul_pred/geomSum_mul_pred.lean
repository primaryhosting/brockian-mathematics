import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma geomSum_mul_pred (p a : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  have h := geom_sum_mul (x := (p : ℤ)) (n := a + 1)
  simp at h
  have h2 : (∑ i ∈ Finset.range (a + 1), (p : ℤ) ^ i) = (∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) := by simp
  rw [h2] at h
  have h3 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have h4 : ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) * (p - 1 : ℕ) + 1 : ℤ) = (p ^ (a + 1) : ℤ) := by
    simp only [h3]
    linarith
  exact_mod_cast h4

/-- For `p ≥ 3` and `q ≥ 5` we have `p * q ≤ 2 * ((p - 1) * (q - 1))`. -/
