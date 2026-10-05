/-
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib


namespace QC

open Matrix

/-- The CNOT gate on two qubits, as a `4 × 4` complex matrix in the
computational basis `|00⟩, |01⟩, |10⟩, |11⟩` (first qubit is the control). -/

theorem cnot_unitary_involutive :
    cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot * cnot = 1 := by
  have hsq : cnot * cnot = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, ?_, hsq⟩ <;> rw [cnot_conjTranspose] <;> exact hsq

/-- CNOT as an element of the unitary group of `4 × 4` complex matrices. -/
