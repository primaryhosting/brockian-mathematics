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

def solid (S : Set E3) : Set E3 := {x | ‖x‖ ≤ 1 ∧ (x = 0 ∨ ‖x‖⁻¹ • x ∈ S)}

/-- The area of a subset of the unit sphere, defined as three times the volume of the
solid cone over it.  (For the whole sphere this gives `4 * π`, see `sphArea_sphere`.) -/
