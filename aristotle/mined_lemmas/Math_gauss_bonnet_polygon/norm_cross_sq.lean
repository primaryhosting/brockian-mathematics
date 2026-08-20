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

lemma norm_cross_sq (x y : E3) : ‖cross x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cross_cross, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  ring_nf
  rw [real_inner_comm y x]
  ring

/-- The solid cone over a subset of the unit sphere. -/
