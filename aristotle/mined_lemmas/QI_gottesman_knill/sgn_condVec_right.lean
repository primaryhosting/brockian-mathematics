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

lemma sgn_condVec_right (z : Bits n) (c : Bool) (j : Fin n) :
    sgn z (condVec c j) = if c then sgn1 (z j) true else 1 := by
  unfold sgn
  rw [Finset.prod_eq_single j]
  · cases c <;> simp [sgn1]
  · intro i _ hij
    rw [condVec_of_ne hij]
    simp [sgn1]
  · intro h; exact absurd (Finset.mem_univ j) h

