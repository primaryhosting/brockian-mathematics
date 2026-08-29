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

private theorem toLp_preimage_wedgeStd (t : ℝ) :
    (WithLp.toLp 2) ⁻¹' (wedgeStd t) = wedgePi t := by
  ext y
  have hnorm : ‖(WithLp.toLp 2 y : E3)‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; congr 1; simp [Fin.sum_univ_three]
  simp only [Set.mem_preimage, wedgeStd, wedgePi, Set.mem_setOf_eq, hnorm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2),
      Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1

