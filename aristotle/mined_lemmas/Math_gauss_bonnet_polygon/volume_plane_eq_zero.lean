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

theorem volume_plane_eq_zero (n : E3) (hn : n ≠ 0) : volume {x : E3 | ⟪n, x⟫ = 0} = 0 := by
  have h : {x : E3 | ⟪n, x⟫ = 0}
      = ((LinearMap.ker ((innerSL ℝ n : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) : Submodule ℝ E3) : Set E3) := by
    ext x; simp [LinearMap.mem_ker]
  rw [h]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : n ∈ (LinearMap.ker ((innerSL ℝ n : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) : Submodule ℝ E3) :=
    htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker] at hmem
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hmem
  exact hn hmem

/-- Splitting a set by the sign of a linear functional does not change its volume. -/
