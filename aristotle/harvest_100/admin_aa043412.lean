/-
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
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

open scoped Matrix

/-- The controlled-NOT gate, as a `4 × 4` complex matrix acting on the two-qubit
computational basis `|00⟩, |01⟩, |10⟩, |11⟩`: it flips the second (target) qubit
exactly when the first (control) qubit is `1`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is unitary (both `Cᴴ * C = 1` and `C * Cᴴ = 1`) and involutive (`C * C = 1`). -/
theorem cnot_unitary_involutive :
    cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot * cnot = 1 := by
  have hH : cnotᴴ = cnot := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.conjTranspose_apply]
  have hsq : cnot * cnot = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.mul_apply, Fin.sum_univ_four]
  have h1 : cnotᴴ * cnot = 1 := by rw [hH]; exact hsq
  have h2 : cnot * cnotᴴ = 1 := by rw [hH]; exact hsq
  exact ⟨Matrix.mem_unitaryGroup_iff'.2 h1, h1, h2, hsq⟩

end QC

