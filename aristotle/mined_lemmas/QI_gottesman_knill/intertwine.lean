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

lemma intertwine (g : Gate n) (p : Pauli n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) * matP p = matP (stepGate g p) * matGate g := by
  cases g with
  | H j => exact intertwine_H j p
  | S j => exact intertwine_S j p
  | CX j k h => exact intertwine_CX j k h p

