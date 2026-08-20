import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma log_le_harmonic_sum (z : ℕ) : Real.log z ≤ ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
  have h := log_add_one_le_harmonic z
  have h2 : ((harmonic z : ℚ) : ℝ) = ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by rw [one_div])
  rw [h2] at h
  refine le_trans ?_ h
  apply Real.log_le_log_of_le
  · push_cast; linarith
  · push_cast; linarith

/-- Euler's upper bound `∏_{p ≤ z} (1 - 1/p) ≤ 2 / log z`. -/
