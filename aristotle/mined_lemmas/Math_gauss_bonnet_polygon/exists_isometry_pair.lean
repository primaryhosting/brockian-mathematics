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

lemma exists_isometry_pair {e f e' f' : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (he' : ‖e'‖ = 1) (hf' : ‖f'‖ = 1) (he'f' : ⟪e', f'⟫ = 0) :
    ∃ L : E3 ≃ₗᵢ[ℝ] E3, L e = e' ∧ L f = f' := by
  obtain ⟨b, hb0, hb1⟩ := exists_onb_pair e f he hf hef
  obtain ⟨b', hb'0, hb'1⟩ := exists_onb_pair e' f' he' hf' he'f'
  refine ⟨b.repr.trans b'.repr.symm, ?_, ?_⟩
  · rw [← hb0, ← hb'0]; simp
  · rw [← hb1, ← hb'1]; simp

