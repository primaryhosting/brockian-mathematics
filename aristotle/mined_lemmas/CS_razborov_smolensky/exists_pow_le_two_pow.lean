import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem exists_pow_le_two_pow (C e : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ C * k ^ e ≤ 2 ^ k := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) e (by norm_num : (1:ℝ) < 2)
  have hC : (0:ℝ) < 1 / (C + 1) := by positivity
  obtain ⟨k, hk, hk1⟩ := ((h.def hC).and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨k, hk1, ?_⟩
  have h2 : ‖((k : ℝ)) ^ e‖ ≤ (1 / (C + 1)) * ‖(2 : ℝ) ^ k‖ := hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h2
  have h3 : (C : ℝ) * (k : ℝ) ^ e ≤ 2 ^ k := by
    have hpos : (0:ℝ) < C + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at h2
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) e]
  exact_mod_cast h3

/-! ### Weights -/

/-- The number of ones of a point of the cube. -/
