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

theorem volume_cell2 (n m : E3) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hlt : ⟪n, m⟫ ^ 2 < 1) :
    volume (cell2 n m) = ENNReal.ofReal (2 * (π - angle n m) / 3) := by
  rw [volume_cell2_eq_wedgeGen, volume_wedgeGen n m hn hm hlt]

/-- The cells for the opposite normals are the antipodal images, hence have the same volume. -/
