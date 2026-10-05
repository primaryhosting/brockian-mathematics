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

lemma sgn_ne_zero (z b : Bits n) : sgn z b ≠ 0 := by
  intro h
  have := sgn_mul_self z b
  rw [h] at this
  simp at this

/-! ## Pauli operators -/

/-- An `n`-qubit Pauli operator, stored as a phase in `{1,i,-1,-i}` together with the
`X`-part and `Z`-part bit strings: it denotes `i^ph · X^xs · Z^zs`. -/
structure Pauli (n : ℕ) where
  /-- the power of `i` in the phase -/
  ph : Fin 4
  /-- the `X`-part -/
  xs : Bits n
  /-- the `Z`-part -/
  zs : Bits n
deriving DecidableEq

/-- The matrix of a Pauli operator in the computational basis. -/
