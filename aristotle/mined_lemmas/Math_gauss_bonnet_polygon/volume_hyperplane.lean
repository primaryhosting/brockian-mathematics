import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_hyperplane (n : E3) (hn : n ≠ 0) : volume {x : E3 | ⟪x, n⟫ = 0} = 0 := by
  have hset : {x : E3 | ⟪x, n⟫ = 0}
      = ((LinearMap.ker (innerSL ℝ n).toLinearMap : Submodule ℝ E3) : Set E3) := by
    ext x
    simp [LinearMap.mem_ker, real_inner_comm x n]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [h]; trivial
  simp only [LinearMap.mem_ker] at hmem
  exact hn (by simpa using hmem)

/-- Splitting a set along a hyperplane through the origin. -/
