import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

noncomputable def sphericalArea (S : Set E3) : ℝ := 3 * (volume (Ioo (0 : ℝ) 1 • S)).toReal

/-- The geodesic (spherical) triangle with vertices `u`, `v`, `w` on the unit sphere: the
points of the sphere lying in the convex cone spanned by `u`, `v` and `w`. -/
