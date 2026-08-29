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

lemma eq_bxor_condVec_of_agreeOff {j : Fin n} {b u : Bits n} (h : agreeOff j b u) :
    b = bxor u (condVec (xor (u j) (b j)) j) := by
  rw [← update_eq_bxor]
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · rw [Function.update_of_ne hi]; exact h i hi

