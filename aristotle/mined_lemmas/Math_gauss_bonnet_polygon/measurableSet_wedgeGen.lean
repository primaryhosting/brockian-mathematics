/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem measurableSet_wedgeGen (n m : E3) : MeasurableSet (wedgeGen n m) := by
  have : wedgeGen n m = {x : E3 | ‖x‖ ≤ 1} ∩
      ({x : E3 | 0 < ⟪n, x⟫} ∩ {x : E3 | 0 < ⟪m, x⟫}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

/-- An orthonormal basis whose first two vectors are two prescribed orthonormal vectors. -/
