import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_wedge (a p q : E3) (ha : ‖a‖ = 1) (hp : ⟪a, p⟫ = 0) (hq : ⟪a, q⟫ = 0)
    (hpq : LinearIndependent ℝ ![p, q]) :
    volume ({x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • p + t • q + r • a} ∩ ball 0 1)
      = ENNReal.ofReal (2 * angle p q / 3) := by
  obtain ⟨b1, b2, hb1, hb2, hab1, hab2, hb12, hpb, hqb⟩ := wedge_frame a p q hp hq hpq
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 (hpq.ne_zero 0)
  have hnq : 0 < ‖q‖ := norm_pos_iff.2 (hpq.ne_zero 1)
  have hsin : 0 < Real.sin (angle p q) := sin_angle_pos p q hpq
  have hset : {x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • p + t • q + r • a}
      = {x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • (‖p‖ • b1) +
          t • ((‖q‖ * Real.cos (angle p q)) • b1 + (‖q‖ * Real.sin (angle p q)) • b2)
          + r • a} := by
    conv_lhs => rw [hpb, hqb]
  rw [hset]
  exact volume_wedge_of_frame a b1 b2 (angle p q) ‖p‖ ‖q‖ ha hb1 hb2 hab1 hab2 hb12 hnp hnq
    (angle_nonneg p q) (angle_le_pi p q) hsin

end Math

import Mathlib

open MeasureTheory Set Real
open scoped ENNReal

namespace Math

/-- The measure of the intersection of `Ioo (-π) π` with `Icc 0 psi`, for `0 ≤ psi ≤ π`. -/
