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

lemma qft_col_orthogonal (n : ℕ) (j k : Fin (2 ^ n)) :
    ∑ m : Fin (2 ^ n), (starRingEnd ℂ) (qft n m j) * qft n m k = if j = k then 1 else 0 := by
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hsq : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = (2 : ℂ) ^ n := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpow]
    push_cast
    ring
  have hNC : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  set d : ℤ := (k : ℕ) - (j : ℕ) with hd
  have hterm : ∀ m : Fin (2 ^ n), (starRingEnd ℂ) (qft n m j) * qft n m k
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℕ) : ℂ) * (d : ℂ)) / ((2 : ℂ) ^ n)) /
        ((2 : ℂ) ^ n) := by
    intro m
    rw [conj_qft_apply, qft, div_mul_div_comm, ← Complex.exp_add, hsq]
    congr 2
    rw [hd]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.sum_div]
  by_cases hjk : j = k
  · subst hjk
    have hd0 : d = 0 := by simp [hd]
    simp only [hd0, Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  · have hdvd : ¬ (((2 ^ n : ℕ) : ℤ) ∣ d) := by
      intro hdv
      apply hjk
      have hj : (j : ℕ) < 2 ^ n := j.isLt
      have hk : (k : ℕ) < 2 ^ n := k.isLt
      have habs : |d| < ((2 ^ n : ℕ) : ℤ) := by
        rw [hd, abs_lt]
        omega
      have hd0 := Int.eq_zero_of_abs_lt_dvd hdv habs
      rw [hd] at hd0
      have : (k : ℕ) = (j : ℕ) := by omega
      exact Fin.ext this.symm
    have hzero := sum_exp_eq_zero (N := 2 ^ n) (Nat.two_pow_pos n) d hdvd
    rw [show ((2 ^ n : ℕ) : ℂ) = (2 : ℂ) ^ n by push_cast; ring] at hzero
    have hcast : ∑ m : Fin (2 ^ n),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℕ) : ℂ) * (d : ℂ)) / ((2 : ℂ) ^ n))
        = ∑ m ∈ Finset.range (2 ^ n),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) / ((2 : ℂ) ^ n)) :=
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) /
          ((2 : ℂ) ^ n))) (2 ^ n)
    rw [hcast, hzero, zero_div, if_neg hjk]

/-- The 7-qubit quantum Fourier transform matrix is unitary. -/
