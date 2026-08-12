/-
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Simp-normal form for products of `2 × 2` matrices given by `!![..]` literals. -/
private lemma pauli_ext_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A = B ↔ A 0 0 = B 0 0 ∧ A 0 1 = B 0 1 ∧ A 1 0 = B 1 0 ∧ A 1 1 = B 1 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> assumption

/-- `X * X = 1`. -/
theorem X_sq : X * X = 1 := by
  simp [pauli_ext_iff, X]

/-- `Y * Y = 1`. -/
theorem Y_sq : Y * Y = 1 := by
  simp [pauli_ext_iff, Y, Complex.I_mul_I]

/-- `Z * Z = 1`. -/
theorem Z_sq : Z * Z = 1 := by
  simp [pauli_ext_iff, Z]

/-- `X` and `Y` anticommute. -/
theorem XY_anticomm : X * Y + Y * X = 0 := by
  simp [pauli_ext_iff, X, Y]

/-- `Y` and `Z` anticommute. -/
theorem YZ_anticomm : Y * Z + Z * Y = 0 := by
  simp [pauli_ext_iff, Y, Z]

/-- `X` and `Z` anticommute. -/
theorem XZ_anticomm : X * Z + Z * X = 0 := by
  simp [pauli_ext_iff, X, Z]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute, and each squares to the
identity matrix. -/
theorem pauli_anticommute :
    (X * Y + Y * X = 0) ∧ (Y * Z + Z * Y = 0) ∧ (X * Z + Z * X = 0) ∧
    (X * X = 1) ∧ (Y * Y = 1) ∧ (Z * Z = 1) :=
  ⟨XY_anticomm, YZ_anticomm, XZ_anticomm, X_sq, Y_sq, Z_sq⟩

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

