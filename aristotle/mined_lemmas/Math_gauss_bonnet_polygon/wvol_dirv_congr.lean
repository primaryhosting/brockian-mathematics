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

lemma wvol_dirv_congr {e f e' f' : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (he' : ‖e'‖ = 1) (hf' : ‖f'‖ = 1) (he'f' : ⟪e', f'⟫ = 0) (α β : ℝ) :
    wvol (dirv e f α) (dirv e f β) = wvol (dirv e' f' α) (dirv e' f' β) := by
  obtain ⟨L, hLe, hLf⟩ := exists_isometry_pair he hf hef he' hf' he'f'
  have hL : ∀ φ : ℝ, L (dirv e f φ) = dirv e' f' φ := by
    intro φ
    simp [dirv, hLe, hLf]
  rw [wvol, wvol, ← hL α, ← hL β, ← image_HS, ← image_HS, ← Set.image_inter L.injective,
    bvol_image]

/-- Every wedge cut out by two half-spaces in a common rotating family has the standard volume. -/
