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

lemma additive_mono (hnn : ∀ θ, 0 ≤ W θ) (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π) : W x ≤ W y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_refl _
  rcases eq_or_lt_of_le hx with rfl | hx'
  · rw [hzero]; exact hnn y
  · have h := hadd x (y - x) hx' (by linarith) (by linarith)
    rw [show x + (y - x) = y by ring] at h
    rw [h]
    linarith [hnn (y - x)]

/-- Additivity for natural multiples. -/
