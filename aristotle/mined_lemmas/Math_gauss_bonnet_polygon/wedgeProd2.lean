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

private def wedgeProd2 (t : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 - p.1 ^ 2 ∧ 0 < p.2.1 ∧
    0 < p.2.1 * Real.cos t + p.2.2 * Real.sin t}

