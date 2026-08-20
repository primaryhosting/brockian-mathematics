import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

theorem angle_cross_cross (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    angle (cross B C) (cross C A) = π - sphAngle C A B := by
  have hAC : ⟪A, C⟫ = ⟪C, A⟫ := real_inner_comm C A
  have hBC : ⟪B, C⟫ = ⟪C, B⟫ := real_inner_comm C B
  have hBA : ⟪B, A⟫ = ⟪A, B⟫ := real_inner_comm A B
  have hn1 : ‖cross B C‖ = √(1 - ⟪C, B⟫ ^ 2) := by
    have h : ‖cross B C‖ ^ 2 = 1 - ⟪C, B⟫ ^ 2 := by rw [norm_cross_sq, hB, hC, hBC]; ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hn2 : ‖cross C A‖ = √(1 - ⟪C, A⟫ ^ 2) := by
    have h : ‖cross C A‖ ^ 2 = 1 - ⟪C, A⟫ ^ 2 := by rw [norm_cross_sq, hC, hA]; ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hi : ⟪cross B C, cross C A⟫ = ⟪C, B⟫ * ⟪C, A⟫ - ⟪A, B⟫ := by
    rw [inner_cross_cross, real_inner_self_eq_norm_sq, hC, hBC, hBA]; ring
  have ha : ‖A - ⟪C, A⟫ • C‖ = √(1 - ⟪C, A⟫ ^ 2) := by
    have h : ‖A - ⟪C, A⟫ • C‖ ^ 2 = 1 - ⟪C, A⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hA, hC, hAC]
      simp
      ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hb : ‖B - ⟪C, B⟫ • C‖ = √(1 - ⟪C, B⟫ ^ 2) := by
    have h : ‖B - ⟪C, B⟫ • C‖ ^ 2 = 1 - ⟪C, B⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hB, hC, hBC]
      simp
      ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hab : ⟪A - ⟪C, A⟫ • C, B - ⟪C, B⟫ • C⟫ = ⟪A, B⟫ - ⟪C, A⟫ * ⟪C, B⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hC, hAC]
    ring
  show Real.arccos _ = π - Real.arccos _
  rw [hi, hn1, hn2, hab, ha, hb, ← Real.arccos_neg]
  congr 1
  rw [mul_comm (√(1 - ⟪C, B⟫ ^ 2)), ← neg_div]
  ring_nf

end Math

import RequestProject.GaussBonnet.Defs

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file computes the volume of a solid wedge (the intersection of the unit ball of `E3`
with two half spaces through the origin).
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric Pointwise

namespace Math

/-- The volume of the unit ball of `E3`. -/
