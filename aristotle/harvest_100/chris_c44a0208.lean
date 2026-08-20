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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The Pauli `X` matrix. -/
def PauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def PauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def PauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute, and each squares to the
identity matrix. -/
theorem pauli_anticommute :
    PauliX * PauliY + PauliY * PauliX = 0 ∧
    PauliY * PauliZ + PauliZ * PauliY = 0 ∧
    PauliX * PauliZ + PauliZ * PauliX = 0 ∧
    PauliX * PauliX = 1 ∧
    PauliY * PauliY = 1 ∧
    PauliZ * PauliZ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [PauliX, PauliY, PauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

end QC

