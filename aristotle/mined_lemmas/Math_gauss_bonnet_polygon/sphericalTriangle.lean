import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

def sphericalTriangle (u v w : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • u + b • v + c • w}

/-- The angle at the vertex `p` of the geodesic triangle with vertices `p`, `a`, `b`: the
angle between the initial velocities at `p` of the geodesics from `p` to `a` and from `p`
to `b`, i.e. between the projections of `a` and `b` to the tangent space at `p`. -/
