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

lemma image_HS (L : E3 ≃ₗᵢ[ℝ] E3) (n : E3) : L '' (HS n) = HS (L n) := by
  ext x
  simp only [Set.mem_image, mem_HS]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [L.inner_map_map]
  · intro hx
    refine ⟨L.symm x, ?_, by simp⟩
    have : ⟪L (L.symm x), L n⟫ = ⟪L.symm x, n⟫ := L.inner_map_map _ _
    rw [L.apply_symm_apply] at this
    rw [← this]; exact hx

end Math

import RequestProject.Basic
import RequestProject.Cauchy

/-!
# The volume of a solid wedge of the unit ball

For two unit vectors `u`, `v` the set of points of the closed unit ball lying in both half-spaces
`⟪x, u⟫ ≥ 0` and `⟪x, v⟫ ≥ 0` is a wedge of dihedral angle `π - angle u v`; its volume is
`2/3 * (π - angle u v)`.
-/

open MeasureTheory Metric InnerProductGeometry
open scoped RealInnerProductSpace Real

noncomputable section

namespace Math

/-- The unit vector at angle `φ` in the plane spanned by the orthonormal pair `(e, f)`. -/
