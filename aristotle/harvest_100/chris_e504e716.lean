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
def PauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def PauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

lemma sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

/-- `H = (X + Z)/√2`. -/
theorem hadamard_eq_XZ : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (PauliX + PauliZ) := by
  unfold H PauliX PauliZ
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `H * X * H = Z`. -/
theorem hadamard_conj_X : H * PauliX * H = PauliZ := by
  unfold H PauliX PauliZ
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hinv : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, sqrt_two_sq]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf

/-- **Hadamard XZ**: `H = (X + Z)/√2` and `H * X * H = Z`. -/
theorem hadamard_XZ :
    H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (PauliX + PauliZ) ∧ H * PauliX * H = PauliZ :=
  ⟨hadamard_eq_XZ, hadamard_conj_X⟩

end QC

#print axioms QC.hadamard_XZ

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

