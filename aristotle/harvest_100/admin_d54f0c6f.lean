/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` gate. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate `H = (1/√2) * !![1, 1; 1, -1]`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / Real.sqrt 2, 1 / Real.sqrt 2; 1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-- `(√2 : ℂ)⁻¹ ^ 2 = 1/2`. -/
lemma inv_sq_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 2⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Real.sqrt_inv,
    Real.sq_sqrt (by norm_num : (2:ℝ)⁻¹ ≥ 0)]
  norm_num

/-- The Hadamard gate equals `(X + Z)/√2`. -/
theorem hadamard_eq_add_div_sqrt_two : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, X, Z]

/-- Conjugating `X` by the Hadamard gate yields `Z`. -/
theorem hadamard_conj_X : H * X * H = Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, X, Z, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;>
      rw [inv_sq_sqrt_two] <;> norm_num

/-- **Hadamard XZ**: `H = (X + Z)/√2`, and `H X H = Z`. -/
theorem hadamard_XZ : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z) ∧ H * X * H = Z :=
  ⟨hadamard_eq_add_div_sqrt_two, hadamard_conj_X⟩

end QC

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

