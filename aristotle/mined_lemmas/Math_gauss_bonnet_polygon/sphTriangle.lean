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

def sphTriangle (A B C : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C}

/-- The interior angle at the vertex `A` of the spherical triangle `A B C`: the Euclidean
angle between the tangent vectors at `A` of the geodesics `A → B` and `A → C`, i.e. between
the projections of `B` and `C` to the plane orthogonal to `A`. -/
