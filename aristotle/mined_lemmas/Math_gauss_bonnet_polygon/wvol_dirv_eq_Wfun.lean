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

lemma wvol_dirv_eq_Wfun {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (s t : ℝ) :
    wvol (dirv e f (s + π / 2)) (dirv e f (t - π / 2)) = Wfun (t - s) := by
  have h1 : ‖dirv e f s‖ = 1 := norm_dirv he hf hef s
  have h2 : ‖dirv e f (s + π / 2)‖ = 1 := norm_dirv he hf hef _
  have h3 : ⟪dirv e f s, dirv e f (s + π / 2)⟫ = 0 := inner_dirv_shift_pair he hf hef s
  have k1 : dirv e f (s + π / 2) = dirv (dirv e f s) (dirv e f (s + π / 2)) (π / 2) := by
    rw [dirv_shift]
  have k2 : dirv e f (t - π / 2)
      = dirv (dirv e f s) (dirv e f (s + π / 2)) ((t - s) - π / 2) := by
    rw [dirv_shift]
    ring_nf
  rw [k1, k2, wvol_dirv_congr h1 h2 h3 norm_e₀ norm_f₀ inner_e₀_f₀]
  rfl

/-- Half of the unit ball. -/
