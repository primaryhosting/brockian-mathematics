import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

def lune (k l : E3 →ₗ[ℝ] ℝ) : Set E3 := ball 0 1 ∩ {x | 0 ≤ k x} ∩ {x | 0 ≤ l x}

/-- The solid octant of the unit ball determined by three linear functionals. -/
