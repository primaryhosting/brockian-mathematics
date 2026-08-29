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

theorem measurableSet_planeSector (t R : ℝ) : MeasurableSet (planeSector t R) := by
  have : planeSector t R = {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2} ∩
      ({w : ℝ × ℝ | 0 < w.1} ∩ {w : ℝ × ℝ | 0 < w.1 * Real.cos t + w.2 * Real.sin t}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

/-- In polar coordinates, the sector is the product of a radius interval and an angle interval. -/
