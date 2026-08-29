/-
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
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

set_option grind.warning false

namespace QC

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `X * X = I`. -/
theorem pauliX_sq : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [pauliX, Matrix.one_fin_two]

/-- `Y * Y = I`. -/
theorem pauliY_sq : pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [pauliY, Matrix.one_fin_two, Complex.I_mul_I]

/-- `Z * Z = I`. -/
theorem pauliZ_sq : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [pauliZ, Matrix.one_fin_two]

/-- `X` and `Y` anticommute. -/
theorem pauliX_pauliY_anticomm : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY]

/-- `Y` and `Z` anticommute. -/
theorem pauliY_pauliZ_anticomm : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, pauliZ]

/-- `X` and `Z` anticommute. -/
theorem pauliX_pauliZ_anticomm : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ]

/--
**Pauli anticommutation relations.**

The three Pauli matrices `X`, `Y`, `Z` pairwise anticommute
(`A * B + B * A = 0` for distinct `A, B`), and each squares to the identity.
-/
theorem pauli_anticommute :
    (pauliX * pauliY + pauliY * pauliX = 0) ∧
    (pauliY * pauliZ + pauliZ * pauliY = 0) ∧
    (pauliZ * pauliX + pauliX * pauliZ = 0) ∧
    (pauliX * pauliX = 1) ∧
    (pauliY * pauliY = 1) ∧
    (pauliZ * pauliZ = 1) :=
  ⟨pauliX_pauliY_anticomm, pauliY_pauliZ_anticomm,
    by rw [add_comm]; exact pauliX_pauliZ_anticomm,
    pauliX_sq, pauliY_sq, pauliZ_sq⟩

end QC

