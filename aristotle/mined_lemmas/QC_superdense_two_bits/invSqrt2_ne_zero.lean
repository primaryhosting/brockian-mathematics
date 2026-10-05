/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

noncomputable section

/-- Pauli `X` gate. -/

lemma invSqrt2_ne_zero : invSqrt2 ≠ 0 := by
  simp [invSqrt2]

/-- The Bell state `(|00⟩ + |11⟩)/√2` on two qubits. -/
