/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

lemma qft_geom_sum {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k : Fin N, ((qftRoot N) ^ (l.val) * ((qftRoot N) ^ (j.val))⁻¹) ^ (k.val)
      = if j = l then (N : ℂ) else 0 := by
  set ζ := qftRoot N
  set x : ℂ := ζ ^ (l.val) * (ζ ^ (j.val))⁻¹ with hx
  have hprim : IsPrimitiveRoot ζ N := qftRoot_isPrimitiveRoot hN
  have hζ0 : ζ ≠ 0 := qftRoot_ne_zero N
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k) N]
  by_cases h : j = l
  · subst h
    have : x = 1 := by
      rw [hx]
      field_simp
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro hx1
      apply h
      have hzp : ζ ^ ((l.val : ℤ) - (j.val : ℤ)) = 1 := by
        rw [zpow_sub₀ hζ0]
        simpa [zpow_natCast, div_eq_mul_inv] using hx1
      have hdvd := (hprim.zpow_eq_one_iff_dvd _).1 hzp
      have hj := j.isLt
      have hl := l.isLt
      have hlt : |(l.val : ℤ) - (j.val : ℤ)| < (N : ℤ) := by
        rw [abs_lt]; omega
      have h0 : (l.val : ℤ) - (j.val : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      have : l.val = j.val := by omega
      exact (Fin.ext this).symm
    have hxN : x ^ N = 1 := by
      have h1 : ζ ^ N = 1 := hprim.pow_eq_one
      have h2 : ∀ m : ℕ, (ζ ^ m) ^ N = 1 := by
        intro m
        rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
      rw [hx, mul_pow, inv_pow, h2, h2, inv_one, mul_one]
    rw [geom_sum_eq hx1, hxN]
    simp [h]

