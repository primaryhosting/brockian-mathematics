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
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The three Pauli matrices pairwise anticommute, and each squares to the identity. -/
theorem pauli_anticommute :
    X * Y = -(Y * X) ∧ Y * Z = -(Z * Y) ∧ Z * X = -(X * Z) ∧
      X * X = 1 ∧ Y * Y = 1 ∧ Z * Z = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

end QC

