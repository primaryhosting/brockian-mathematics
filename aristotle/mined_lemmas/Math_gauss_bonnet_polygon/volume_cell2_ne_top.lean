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

theorem volume_cell2_ne_top (n m : E3) : volume (cell2 n m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (le_trans Set.inter_subset_left
    Set.inter_subset_left : cell2 n m ⊆ ball (0 : E3) 1))
  rw [volume_ball_one]
  exact ENNReal.ofReal_ne_top

/-- The solid lune has the same volume as the corresponding closed wedge. -/
