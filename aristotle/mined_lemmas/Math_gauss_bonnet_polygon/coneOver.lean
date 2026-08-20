import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

def coneOver (S : Set E3) : Set E3 := {x : E3 | ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ y ∈ S, x = r • y}

/-- The area of a subset of the unit sphere, defined as three times the volume of the cone over
it.  With this normalisation the whole unit sphere has area `4 * π`,
see `Math.sphArea_unit_sphere`. -/
