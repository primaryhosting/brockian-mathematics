/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The `3 × 3` sine-kernel Hankel matrix. -/
def M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `M`. -/
def Minv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

lemma det_M : M.det = 5/108 := by
  simp [M, Matrix.det_fin_three]
  norm_num

lemma M_mul_Minv : M * Minv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Minv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num

lemma Minv_eq : M⁻¹ = Minv := by
  refine Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check: `M` is invertible (its determinant is `5/108 ≠ 0`) and
`(M⁻¹)₀₀ = 36/5`, so `1 / (eᵀ₀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio
Christoffel value `Λ₂(0;1) = 5/36`. -/
theorem christoffel_inverse_form :
    M.det = 5/108 ∧ IsUnit M.det ∧ M⁻¹ 0 0 = 36/5 ∧ (M⁻¹ 0 0)⁻¹ = 5/36 := by
  refine ⟨det_M, ?_, ?_, ?_⟩
  · rw [det_M]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [Minv_eq]; simp [Minv]
  · rw [Minv_eq]; norm_num [Minv]

end Zeta23Scaffold

