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

lemma matGate_H_mul_self (j : Fin n) :
    (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) * matGate (Gate.H j) = 1 := by
  funext b c
  rw [Matrix.mul_apply]
  rw [sum_eq_pair j _ b (fun d hd => ?_)]
  · have e1 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) b
        (Function.update b j v) = invSqrt2 * sgn1 (b j) v := by
      intro v
      rw [matGate_H_apply, if_pos (agreeOff_update j b v)]
      simp
    by_cases hbc : agreeOff j b c
    · have e2 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
          (Function.update b j v) c = invSqrt2 * sgn1 v (c j) := by
        intro v
        rw [matGate_H_apply,
          if_pos (agreeOff_trans (agreeOff_symm (agreeOff_update j b v)) hbc)]
        simp
      have key : ∀ u w : Bool, invSqrt2 * sgn1 u false * (invSqrt2 * sgn1 false w)
            + invSqrt2 * sgn1 u true * (invSqrt2 * sgn1 true w)
          = if u = w then 1 else 0 := by
        intro u w
        cases u <;> cases w <;> norm_num [sgn1] <;>
          first
            | linear_combination (2 : ℂ) * invSqrt2_mul_self
            | ring
      rw [e1, e1, e2, e2, key, Matrix.one_apply]
      by_cases hj : b j = c j
      · rw [if_pos hj, if_pos (eq_of_agreeOff hbc hj)]
      · rw [if_neg hj, if_neg (fun hh => hj (by rw [hh]))]
    · have e2 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
          (Function.update b j v) c = 0 := by
        intro v
        rw [matGate_H_apply, if_neg]
        intro hh
        exact hbc (agreeOff_trans (agreeOff_update j b v) hh)
      have hne : b ≠ c := by
        intro hh; exact hbc (fun i _ => by rw [hh])
      rw [e2, e2, Matrix.one_apply_ne hne]
      ring
  · rw [matGate_H_apply, if_neg (fun hh => hd (agreeOff_symm hh)), zero_mul]

