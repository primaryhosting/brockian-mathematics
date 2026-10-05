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

lemma Wfun_zero : Wfun 0 = 0 := by
  set g := dirv e₀ f₀ (π / 2) with hg
  have hneg : dirv e₀ f₀ (0 - π / 2) = -g := by
    have hd := dirv_add_pi e₀ f₀ (0 - π / 2)
    rw [show (0 : ℝ) - π / 2 + π = π / 2 by ring] at hd
    rw [hg, hd, neg_neg]
  rw [Wfun, wvol, hneg]
  refine bvol_eq_zero_of_null (measure_mono_null ?_
    (hyperplane_null (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ (π / 2))))
  rintro x ⟨h1, h2⟩
  simp only [mem_HS, inner_neg_right] at h1 h2
  exact le_antisymm (by linarith) h1

