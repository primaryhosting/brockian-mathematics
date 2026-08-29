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

lemma update_eq_bxor (u : Bits n) (j : Fin n) (v : Bool) :
    Function.update u j v = bxor u (condVec (xor (u j) v) j) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [condVec]
  · simp [Function.update_of_ne hi, condVec, hi]

