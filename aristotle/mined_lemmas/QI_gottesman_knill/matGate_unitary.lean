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

lemma matGate_unitary (g : Gate n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) := by
  cases g with
  | H j =>
      rw [Unitary.mem_iff]
      rw [matGate_H_star j]
      exact ⟨matGate_H_mul_self j, matGate_H_mul_self j⟩
  | S j => exact matGate_S_unitary j
  | CX j k h => exact matGate_CX_unitary j k h

/-! ## Heisenberg evolution of Pauli operators -/

