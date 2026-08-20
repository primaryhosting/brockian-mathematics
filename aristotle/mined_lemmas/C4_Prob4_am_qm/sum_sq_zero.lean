import Mathlib
open Finset
namespace C4.Prob4

/-- AM–QM inequality. The nonnegativity hypothesis `hx` is part of the requested
statement, but it is not needed for the proof. -/

theorem sum_sq_zero {n : ℕ} (x : Fin n → ℝ) (h : ∑ i, (x i)^2 = 0) : ∀ i, x i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

