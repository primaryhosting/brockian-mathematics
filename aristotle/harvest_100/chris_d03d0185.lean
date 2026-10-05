/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `√2`, viewed as a complex number. -/
noncomputable def sqrt2 : ℂ := (Real.sqrt 2 : ℝ)

/-- The Hadamard matrix `H`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / sqrt2, 1 / sqrt2; 1 / sqrt2, -(1 / sqrt2)]

lemma sqrt2_ne_zero : sqrt2 ≠ 0 := by
  simp only [sqrt2, ne_eq, Complex.ofReal_eq_zero]
  positivity

lemma sqrt2_sq : sqrt2 * sqrt2 = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [sqrt2, ← Complex.ofReal_mul, h]
  norm_num

/-- `H = (X + Z) / √2`, written with scalar multiplication by `(√2)⁻¹`. -/
theorem H_eq_add_div : H = (sqrt2)⁻¹ • (X + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, X, Z, Matrix.smul_apply, one_div]

/-- `H * X * H = Z`. -/
theorem H_mul_X_mul_H : H * X * H = Z := by
  have hs := sqrt2_sq
  have hne := sqrt2_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, X, Z, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;>
    first
      | linear_combination hs
      | linear_combination -hs

/-- **Hadamard XZ**: `H = (X + Z)/√2` and `H X H = Z`. -/
theorem hadamard_XZ : H = (sqrt2)⁻¹ • (X + Z) ∧ H * X * H = Z :=
  ⟨H_eq_add_div, H_mul_X_mul_H⟩

end QC

