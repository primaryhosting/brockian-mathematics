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

lemma matGate_CX_unitary (j k : Fin n) (h : j ≠ k) :
    (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) ∈
      unitary (Matrix (Bits n) (Bits n) ℂ) := by
  have hstar : star (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ)
      = matGate (Gate.CX j k h) := by
    funext b c
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, matGate]
    by_cases hbc : c = cxf j k b
    · rw [if_pos hbc, if_pos ((cxf_eq_iff j k h b c).2 hbc)]
      simp
    · rw [if_neg hbc, if_neg (fun hh => hbc ((cxf_eq_iff j k h b c).1 hh))]
      simp
  have hmul : (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) * matGate (Gate.CX j k h)
      = 1 := by
    funext b c
    rw [Matrix.mul_apply, Finset.sum_eq_single (cxf j k c)]
    · simp [matGate, cxf_involutive j k h, Matrix.one_apply]
    · intro d _ hd
      simp [matGate, hd]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  rw [Unitary.mem_iff, hstar]
  exact ⟨hmul, hmul⟩

