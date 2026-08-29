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

private def wedgePi (t : ℝ) : Set (Fin 3 → ℝ) :=
  {y | y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≤ 1 ∧ 0 < y 0 ∧ 0 < y 0 * Real.cos t + y 1 * Real.sin t}

