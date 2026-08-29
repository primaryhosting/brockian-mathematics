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

def cell1 (n : E3) : Set E3 := ball 0 1 ∩ cone1 n

/-- The intersection of the open unit ball with two open half-spaces (a solid lune). -/
