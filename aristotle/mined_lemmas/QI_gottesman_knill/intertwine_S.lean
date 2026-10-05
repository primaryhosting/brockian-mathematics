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

lemma intertwine_S (j : Fin n) (p : Pauli n) :
    (matGate (Gate.S j) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.S j) p) * matGate (Gate.S j) := by
  funext b b'
  rw [mul_matP, matP_mul]
  simp only [stepGate, matGate]
  by_cases hb : b = bxor b' p.xs
  · subst hb
    rw [if_pos rfl, if_pos (by simp : bxor (bxor b' p.xs) p.xs = b')]
    rw [I_pow_fin4_add, sgn_bxor_left, sgn_condVec_left]
    simp only [bxor_apply, bxor_cancel_right]
    by_cases hx : p.xs j = true <;> by_cases hbj : b' j = true <;>
      simp [hx, hbj, sgn1, Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_mul_I] <;> ring
  · have hb2 : ¬ (bxor b p.xs = b') := fun hh => hb (by rw [← hh]; simp)
    rw [if_neg hb, zero_mul, if_neg hb2, mul_zero]

