/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
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

namespace QC

/-- The Pauli `X` gate. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

lemma sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `H = (X + Z)/√2`, and `H * X * H = Z`. -/
theorem hadamard_XZ :
    H = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (X + Z) ∧ H * X * H = Z := by
  have hsq := sqrt_two_sq
  constructor
  · unfold H X Z
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
      rw [← mul_inv, hsq]
    unfold H X Z
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]

#print axioms QC.hadamard_XZ

end QC

