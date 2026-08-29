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

theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose_apply]

/-- CNOT is unitary and squares to the identity. -/
