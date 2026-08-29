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

theorem volume_cell2_eq_wedgeGen (n m : E3) : volume (cell2 n m) = volume (wedgeGen n m) := by
  have hsub : cell2 n m ⊆ wedgeGen n m := by
    rintro x ⟨⟨hb, hn⟩, hm⟩
    exact ⟨le_of_lt (by simpa [mem_ball_zero_iff] using hb), hn, hm⟩
  have hsub2 : wedgeGen n m ⊆ cell2 n m ∪ sphere (0 : E3) 1 := by
    rintro x ⟨hb, hn, hm⟩
    rcases eq_or_lt_of_le hb with h | h
    · exact Or.inr (by simp [mem_sphere_zero_iff_norm, h])
    · exact Or.inl ⟨⟨by simpa [mem_ball_zero_iff] using h, hn⟩, hm⟩
  refine le_antisymm (measure_mono hsub) ?_
  calc volume (wedgeGen n m) ≤ volume (cell2 n m ∪ sphere (0 : E3) 1) := measure_mono hsub2
    _ ≤ volume (cell2 n m) + volume (sphere (0 : E3) 1) := measure_union_le _ _
    _ = volume (cell2 n m) := by rw [Measure.addHaar_sphere, add_zero]

/-- **Volume of a solid lune.** -/
