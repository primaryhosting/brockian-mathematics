import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma Wfun_pi : Wfun π = 2 * π / 3 := by
  have h : π - π / 2 = π / 2 := by ring
  rw [Wfun, h, wvol, Set.inter_self]
  exact bvol_HS (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ _)

