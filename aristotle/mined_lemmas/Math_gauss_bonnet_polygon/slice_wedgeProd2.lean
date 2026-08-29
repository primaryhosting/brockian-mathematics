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

private theorem slice_wedgeProd2 (t z : ℝ) :
    (Prod.mk z ⁻¹' wedgeProd2 t) = planeSector t (Real.sqrt (1 - z ^ 2)) := by
  ext w
  simp only [Set.mem_preimage, wedgeProd2, planeSector, Set.mem_setOf_eq]
  by_cases hz : 1 - z ^ 2 < 0
  · constructor
    · rintro ⟨h1, h2, h3⟩; nlinarith
    · rintro ⟨h1, h2, h3⟩
      rw [Real.sqrt_eq_zero_of_nonpos hz.le] at h1
      exact absurd h1 (by nlinarith)
  · push_neg at hz
    rw [Real.sq_sqrt hz]

