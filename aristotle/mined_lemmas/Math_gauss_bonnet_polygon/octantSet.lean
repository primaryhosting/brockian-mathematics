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

def octantSet (u v w : E3) : Set E3 :=
  {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫ ∧ 0 ≤ ⟪x, w⟫}

/-- **Girard's decomposition.**  The six solid lunes determined by three planes through the
origin cover the ball once, except for the two opposite solid triangles, which are covered
three times. -/
