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

lemma inner_nrm (A B C : E3) (hd : ⟪A, cross B C⟫ ≠ 0) :
    ⟪A, nrm A B C⟫ = 1 ∧ ⟪B, nrm A B C⟫ = 0 ∧ ⟪C, nrm A B C⟫ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nrm, real_inner_smul_right, inv_mul_cancel₀ hd]
  · rw [nrm, real_inner_smul_right, real_inner_comm (cross B C) B, inner_cross_self_left, mul_zero]
  · rw [nrm, real_inner_smul_right, real_inner_comm (cross B C) C, inner_cross_self_right, mul_zero]

/-- The three normals form the basis dual to `A`, `B`, `C`. -/
