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

def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 1, 0, 0],
              ![0, 0, 0, 1],
              ![0, 0, 1, 0]]

/-- The CNOT gate is self-adjoint (its conjugate transpose is itself). -/
