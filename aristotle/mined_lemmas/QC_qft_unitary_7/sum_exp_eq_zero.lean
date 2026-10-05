/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`:
`F j k = exp (2πi·jk / 2^n) / √(2^n)`. -/

lemma sum_exp_eq_zero {N : ℕ} (hN : 0 < N) (d : ℤ) (h : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) / (N : ℂ)) = 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ)) with hz
  have hterm : ∀ m : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) / (N : ℂ)) = z ^ m := by
    intro m
    rw [hz, ← Complex.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have hEq : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))
        = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
    rw [hEq]
    exact Complex.exp_int_mul_two_pi_mul_I d
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hz, Complex.exp_eq_one_iff] at h1
    obtain ⟨t, ht⟩ := h1
    refine h ⟨t, ?_⟩
    field_simp at ht
    exact_mod_cast ht
  have hmul := geom_sum_mul z N
  rw [hzN, sub_self] at hmul
  rcases mul_eq_zero.1 hmul with h' | h'
  · exact h'
  · exact absurd (sub_eq_zero.1 h') hz1

/-- Orthonormality of the columns of the QFT matrix. -/
