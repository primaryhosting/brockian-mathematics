import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

lemma sign_count {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (if 0 < B * C then (1:ℝ≥0∞) else 0) + (if 0 < A * C then 1 else 0)
      + (if 0 < A * B then 1 else 0)
      = 1 + 2 * (if (0 < A * B ∧ 0 < B * C) then 1 else 0) := by
  rcases lt_or_gt_of_ne hA with hA' | hA' <;> rcases lt_or_gt_of_ne hB with hB' | hB' <;>
    rcases lt_or_gt_of_ne hC with hC' | hC' <;>
    simp [mul_pos_iff, hA', hB', hC', hA'.asymm, hB'.asymm, hC'.asymm] <;> ring

/-! ### The main theorem -/

/-- **Girard's theorem** (the Gauss-Bonnet formula for a spherical triangle): the sum of the
three interior angles of a nondegenerate geodesic triangle on the unit sphere equals `π` plus
the area of the triangle. -/
