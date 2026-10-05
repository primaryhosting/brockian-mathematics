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

lemma matGate_S_unitary (j : Fin n) :
    (matGate (Gate.S j) : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) := by
  rw [Unitary.mem_iff, matGate_S_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  constructor <;>
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext b
      by_cases hb : b j = true <;>
        simp [hb, Pi.star_apply, Complex.conj_I, Complex.I_mul_I]

