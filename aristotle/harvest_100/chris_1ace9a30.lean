import Mathlib

/-!
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The 2×2 identity matrix. -/
def I2 : Matrix (Fin 2) (Fin 2) ℂ := 1

theorem X_sq : X * X = I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, I2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Y_sq : Y * Y = I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y, I2, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

theorem Z_sq : Z * Z = I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, I2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem XY_anticomm : X * Y + Y * X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Y]

theorem YZ_anticomm : Y * Z + Z * Y = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y, Z]

theorem XZ_anticomm : X * Z + Z * X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute, and each squares to the
identity matrix. -/
theorem pauli_anticommute :
    (X * Y + Y * X = 0) ∧ (Y * Z + Z * Y = 0) ∧ (X * Z + Z * X = 0) ∧
    (X * X = I2) ∧ (Y * Y = I2) ∧ (Z * Z = I2) :=
  ⟨XY_anticomm, YZ_anticomm, XZ_anticomm, X_sq, Y_sq, Z_sq⟩

end QC

