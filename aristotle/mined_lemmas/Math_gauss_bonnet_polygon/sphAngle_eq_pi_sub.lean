/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem sphAngle_eq_pi_sub (a b c : E3) (ha : ‖a‖ = 1) :
    sphAngle a b c = π - InnerProductGeometry.angle (cross c a) (cross a b) := by
  have h1 : ‖cross c a‖ = ‖c - ⟪a, c⟫ • a‖ := norm_cross_right a c ha
  have h2 : ‖cross a b‖ = ‖b - ⟪a, b⟫ • a‖ := by
    rw [cross_swap a b, norm_neg]; exact norm_cross_right a b ha
  have h3 : ⟪cross c a, cross a b⟫ = - ⟪b - ⟪a, b⟫ • a, c - ⟪a, c⟫ • a⟫ := by
    rw [inner_cross_cross]
    simp [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, ha,
      real_inner_comm a b, real_inner_comm a c, real_inner_comm c b]
    ring
  unfold sphAngle InnerProductGeometry.angle
  rw [h1, h2, h3, ← Real.arccos_neg]
  congr 1
  rw [real_inner_comm]
  ring

/-! ### Volumes -/

