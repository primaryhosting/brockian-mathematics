/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/

lemma conj_gate (g : Gate n) (p : Pauli n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) * matP p * star (matGate g)
      = matP (stepGate g p) := by
  rw [intertwine g p, Matrix.mul_assoc, (Unitary.mem_iff.1 (matGate_unitary g)).2, mul_one]

/-! ## Circuits -/

/-- The unitary implemented by a circuit; the head of the list is applied first. -/
