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

lemma intertwine_CX (j k : Fin n) (h : j ≠ k) (p : Pauli n) :
    (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.CX j k h) p) * matGate (Gate.CX j k h) := by
  funext b b'
  rw [mul_matP, matP_mul]
  simp only [stepGate, matGate]
  by_cases hb : b = cxf j k (bxor b' p.xs)
  · have hb2 : bxor b (cxf j k p.xs) = cxf j k b' := by
      rw [hb, cxf_bxor]
      simp
    rw [if_pos hb, if_pos hb2, one_mul, mul_one, hb2, sgn_czf_cxf j k h]
  · have hb2 : ¬ (bxor b (cxf j k p.xs) = cxf j k b') := by
      intro hh
      apply hb
      have hb3 : b = bxor (cxf j k b') (cxf j k p.xs) := by rw [← hh]; simp
      rw [hb3, cxf_bxor]
    rw [if_neg hb, if_neg hb2, zero_mul, mul_zero]

