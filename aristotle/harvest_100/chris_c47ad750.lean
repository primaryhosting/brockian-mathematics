import Mathlib
/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The sine-kernel Hankel matrix of order 3. -/
def M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `M`. -/
def Minv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

lemma M_det : M.det = 5/108 := by
  simp [M, Matrix.det_fin_three]
  norm_num

lemma M_mul_Minv : M * Minv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Minv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

lemma M_inv_eq : M⁻¹ = Minv := Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check for the sine-kernel Hankel matrix: its determinant is
`5/108` (hence nonzero, so the matrix is invertible), and `(M⁻¹) 0 0 = 36/5`, so that
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, agreeing with the determinant-ratio Christoffel value. -/
theorem christoffel_inverse_form :
    M.det = 5/108 ∧ M.det ≠ 0 ∧ IsUnit M.det ∧ (M⁻¹ 0 0 : ℚ) = 36/5 := by
  have hd : M.det = 5/108 := M_det
  refine ⟨hd, by rw [hd]; norm_num, ?_, ?_⟩
  · rw [hd]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [M_inv_eq]; simp [Minv]

end Zeta23Scaffold

#print axioms Zeta23Scaffold.christoffel_inverse_form

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

