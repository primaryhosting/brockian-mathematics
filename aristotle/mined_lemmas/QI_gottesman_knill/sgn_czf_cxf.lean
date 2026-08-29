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

lemma sgn_czf_cxf (j k : Fin n) (h : j ≠ k) (z b : Bits n) :
    sgn (czf j k z) (cxf j k b) = sgn z b := by
  rw [czf, cxf, sgn_bxor_left, sgn_bxor_right, sgn_bxor_right, sgn_condVec_left,
    sgn_condVec_right, sgn_condVec_left]
  have hjk : (decide (j = k)) = false := by simp [h]
  simp only [condVec_apply, hjk, Bool.and_false]
  by_cases hz : z k = true <;> by_cases hbj : b j = true <;> simp [hz, hbj, sgn1]

