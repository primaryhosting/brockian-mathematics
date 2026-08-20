import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem measurableSet_wedge_std (psi : ℝ) :
    MeasurableSet {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧
      0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi} := by measurability

/-- The angle between two linearly independent vectors lies strictly between `0` and `π`. -/
