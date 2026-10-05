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

lemma intertwine_H (j : Fin n) (p : Pauli n) :
    (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.H j) p) * matGate (Gate.H j) := by
  funext b b'
  rw [mul_matP, matP_mul, matGate_H_apply, matGate_H_apply]
  have hstepx : (stepGate (Gate.H j) p).xs
      = bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j) := rfl
  have hstepz : (stepGate (Gate.H j) p).zs
      = bxor p.zs (condVec (xor (p.xs j) (p.zs j)) j) := rfl
  have hstepph : (stepGate (Gate.H j) p).ph
      = p.ph + (if p.xs j && p.zs j then 2 else 0) := rfl
  rw [hstepx, hstepz, hstepph]
  have hiff : agreeOff j b (bxor b' p.xs) ↔
      agreeOff j (bxor b (bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j))) b' := by
    constructor
    · intro hh i hi
      have h1 : b i = xor (b' i) (p.xs i) := hh i hi
      show xor (b i) (xor (p.xs i) (condVec (xor (p.xs j) (p.zs j)) j i)) = b' i
      rw [condVec_of_ne hi, h1]
      simp
    · intro hh i hi
      have h1 : xor (b i) (xor (p.xs i) (condVec (xor (p.xs j) (p.zs j)) j i)) = b' i := hh i hi
      rw [condVec_of_ne hi] at h1
      show b i = xor (b' i) (p.xs i)
      rw [← h1]
      simp
  by_cases hb : agreeOff j b (bxor b' p.xs)
  · rw [if_pos hb, if_pos (hiff.1 hb)]
    have hbu := eq_bxor_condVec_of_agreeOff hb
    have hkey : bxor b (bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j))
        = bxor b' (condVec (xor (xor ((bxor b' p.xs) j) (b j))
            (xor (p.xs j) (p.zs j))) j) := by
      conv_lhs => rw [hbu]
      rw [bxor_shuffle, condVec_bxor_condVec]
    rw [hkey, sgn_bxor_left, sgn_bxor_right, sgn_bxor_right, sgn_condVec_right,
      sgn_condVec_left, sgn_condVec_left, condVec_self, I_pow_fin4_add]
    simp only [bxor_apply, condVec_self]
    by_cases hB : b' j = true <;> by_cases hX : p.xs j = true <;>
      by_cases hZ : p.zs j = true <;> by_cases hv : b j = true <;>
      simp [hB, hX, hZ, hv, sgn1, Complex.I_mul_I] <;> ring
  · rw [if_neg hb, zero_mul, if_neg (fun hh => hb (hiff.2 hh)), mul_zero]

