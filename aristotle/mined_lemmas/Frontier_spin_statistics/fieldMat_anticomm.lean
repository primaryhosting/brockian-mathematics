/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem fieldMat_anticomm {x y : Fin 4 → ℝ} (h : Spacelike x y) :
    fieldMat x * (fieldMat y)ᴴ + (fieldMat y)ᴴ * fieldMat x = 0 := by
  have ho := coeff_orthogonal h
  rw [fieldMat_mul_adj, adj_mul_fieldMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination ho

