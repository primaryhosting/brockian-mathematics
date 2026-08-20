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

theorem inner_cross_ne_zero_of_linearIndependent {a b c : E3}
    (h : LinearIndependent ℝ ![a, b, c]) : ⟪a, cross b c⟫ ≠ 0 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![(a : Fin 3 → ℝ), (b : Fin 3 → ℝ), (c : Fin 3 → ℝ)] with hM
  have hrow : LinearIndependent ℝ M.row := by
    have hr : M.row = fun i => ((EuclideanSpace.equiv (Fin 3) ℝ) (![a, b, c] i)) := by
      funext i
      fin_cases i <;> rfl
    rw [hr]
    exact h.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap (by simp [LinearEquiv.ker])
  have hdet : M.det ≠ 0 := by
    have hU := Matrix.linearIndependent_rows_iff_isUnit.mp hrow
    rw [Matrix.isUnit_iff_isUnit_det] at hU
    exact hU.ne_zero
  have hEq : ⟪a, cross b c⟫ = M.det := by
    simp [hM, cross, PiLp.inner_apply, Fin.sum_univ_three, Matrix.det_fin_three]; ring
  rw [hEq]; exact hdet

/-! ### The angle at a vertex in terms of the normals of the sides -/

/-- The interior angle at the vertex `a` is `π` minus the angle between the two outer normals
of the sides through `a`. -/
