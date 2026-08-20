/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_inner_eq_zero {u : E3} (hu : u ≠ 0) : volume {x : E3 | ⟪u, x⟫ = 0} = 0 := by
  have hset : {x : E3 | ⟪u, x⟫ = 0} = (LinearMap.ker (innerSL ℝ u).toLinearMap : Submodule ℝ E3) := by
    ext x; simp [LinearMap.mem_ker]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : u ∈ LinearMap.ker (innerSL ℝ u).toLinearMap := by rw [h]; trivial
  simp [LinearMap.mem_ker] at hmem
  exact hu hmem

/-- Splitting a set by the hyperplane orthogonal to `u`. -/
