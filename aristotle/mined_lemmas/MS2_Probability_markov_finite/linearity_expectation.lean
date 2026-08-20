import Mathlib
open Finset
namespace MS2.Probability
/-- Finite Markov inequality. The hypothesis `0 < a` is kept as stated, although the
proof does not need it (nonnegativity of `x` alone suffices). -/

theorem linearity_expectation {n : ℕ} (x y : Fin n → ℝ) (p : Fin n → ℝ) :
    ∑ i, p i * (x i + y i) = (∑ i, p i * x i) + (∑ i, p i * y i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => mul_add _ _ _)

