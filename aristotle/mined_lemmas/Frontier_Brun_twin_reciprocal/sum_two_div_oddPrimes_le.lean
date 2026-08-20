import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_two_div_oddPrimes_le (J : ℕ) :
    ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ 1 + 16 * Real.sqrt J := by
  have hsub : oddPrimes (2 ^ J) ⊆ primesLE (2 ^ J) := by
    intro p hp
    rw [mem_oddPrimes] at hp
    exact mem_primesLE.mpr ⟨hp.1, hp.2.1⟩
  have h1 : ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _ _
    positivity
  have h2 : ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) = 2 * ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h3 := sum_inv_primesLE_pow_le J
  have h4 : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ 8 * Real.sqrt J := by
    have : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ ∑ i ∈ Icc 1 J, (4 / i : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      exact Finset.Ico_subset_Icc_self
    have h5 : ∑ i ∈ Icc 1 J, (4 / i : ℝ) = 4 * ∑ i ∈ Icc 1 J, (1 / i : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have := sum_inv_le_two_sqrt J
    linarith
  linarith

end Brun

