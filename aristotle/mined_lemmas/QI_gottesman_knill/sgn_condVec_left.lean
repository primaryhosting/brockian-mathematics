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

lemma sgn_condVec_left (b : Bits n) (c : Bool) (j : Fin n) :
    sgn (condVec c j) b = if c then sgn1 (b j) true else 1 := by
  rw [show sgn (condVec c j) b = sgn b (condVec c j) by
        unfold sgn; exact Finset.prod_congr rfl fun i _ => sgn1_comm _ _]
  exact sgn_condVec_right _ _ _

