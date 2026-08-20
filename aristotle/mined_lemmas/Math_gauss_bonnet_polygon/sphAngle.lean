import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

noncomputable def sphAngle (p a b : E3) : ℝ :=
  angle (a - ⟪p, a⟫ • p) (b - ⟪p, b⟫ • p)

/-! ## Auxiliary lemmas -/

/-- Coordinates with respect to three linearly independent vectors of `ℝ³`. -/
