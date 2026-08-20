import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem measurableSet_halfspace (k : E3 →ₗ[ℝ] ℝ) : MeasurableSet {x : E3 | 0 ≤ k x} :=
  measurableSet_le measurable_const (k.continuous_of_finiteDimensional).measurable

/-- A nonzero linear functional splits any measurable set into two halves. -/
