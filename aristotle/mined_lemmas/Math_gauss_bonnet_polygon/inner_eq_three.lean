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

lemma inner_eq_three (x y : E3) :
    ⟪x, y⟫ = x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1 + x.ofLp 2 * y.ofLp 2 := by
  rw [inner_eq_sum, Fin.sum_univ_three]

/-- Binet–Cauchy identity for the cross product. -/
