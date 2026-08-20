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

theorem solid_sphere : solid (sphere (0 : E3) 1) = closedBall (0 : E3) 1 := by
  ext x
  simp only [solid, Set.mem_setOf_eq, mem_closedBall, dist_zero_right, mem_sphere_iff_norm,
    sub_zero, norm_smul, norm_inv, norm_norm]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (by field_simp [norm_ne_zero_iff.2 hx])

