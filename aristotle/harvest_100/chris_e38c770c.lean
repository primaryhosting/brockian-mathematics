import Mathlib
/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
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

set_option grind.warning false

namespace QC

open Matrix

/-- The controlled-NOT gate, as a `4 × 4` complex matrix acting on the two-qubit
computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is self-adjoint: its conjugate transpose is itself. -/
theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose]

/-- CNOT squares to the identity. -/
theorem cnot_mul_self : cnot * cnot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **CNOT is unitary and involutive.**  Its conjugate transpose is a two-sided
inverse (equivalently, `cnot` lies in the unitary group of `4 × 4` complex
matrices), and `cnot ^ 2 = 1`. -/
theorem cnot_unitary_involutive :
    cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      cnot * cnot = 1 ∧ cnot ^ 2 = 1 := by
  have h : cnotᴴ * cnot = 1 := by rw [cnot_conjTranspose]; exact cnot_mul_self
  have h' : cnot * cnotᴴ = 1 := by rw [cnot_conjTranspose]; exact cnot_mul_self
  refine ⟨h, h', ?_, cnot_mul_self, ?_⟩
  · exact Matrix.mem_unitaryGroup_iff'.2 h
  · rw [pow_two]; exact cnot_mul_self

end QC

