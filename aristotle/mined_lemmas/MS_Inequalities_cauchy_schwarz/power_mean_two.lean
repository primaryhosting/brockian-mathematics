import Mathlib
open Finset
namespace MS.Inequalities

theorem power_mean_two {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 ≤ n * ∑ i, (a i) ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (1 : ℝ)) a
  simpa [Finset.card_univ, mul_comm] using this

