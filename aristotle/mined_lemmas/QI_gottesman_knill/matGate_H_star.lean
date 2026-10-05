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

lemma matGate_H_star (j : Fin n) : star (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
    = matGate (Gate.H j) := by
  funext b c
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, matGate_H_apply]
  by_cases h : agreeOff j b c
  · rw [if_pos (agreeOff_symm h), if_pos h, star_mul', star_invSqrt2, star_sgn1, sgn1_comm]
  · rw [if_neg (fun hh => h (agreeOff_symm hh)), if_neg h, star_zero]

