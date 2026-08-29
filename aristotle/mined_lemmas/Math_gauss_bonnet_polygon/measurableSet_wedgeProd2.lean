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

private theorem measurableSet_wedgeProd2 (t : ℝ) : MeasurableSet (wedgeProd2 t) := by
  have : wedgeProd2 t = {p : ℝ × (ℝ × ℝ) | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 - p.1 ^ 2} ∩
      ({p : ℝ × (ℝ × ℝ) | 0 < p.2.1} ∩
        {p : ℝ × (ℝ × ℝ) | 0 < p.2.1 * Real.cos t + p.2.2 * Real.sin t}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

