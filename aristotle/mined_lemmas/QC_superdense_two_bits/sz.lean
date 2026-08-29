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

def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The encoding gate applied by Alice to her qubit for the message `(a, b)`. -/
