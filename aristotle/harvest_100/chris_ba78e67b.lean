import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N × N` discrete Fourier transform matrix,
`F j k = ω^(j k) / √N` with `ω = exp (2 π i / N)`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => omegaN N ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt N : ℂ)

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := dftMatrix (2 ^ n)

lemma isPrimitiveRoot_omegaN {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (omegaN N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma omegaN_ne_zero (N : ℕ) : omegaN N ≠ 0 := Complex.exp_ne_zero _

lemma conj_omegaN (N : ℕ) : (starRingEnd ℂ) (omegaN N) = (omegaN N)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

lemma sqrt_mul_sqrt (N : ℕ) : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

lemma pow_mul_inv_pow (ω : ℂ) (hω : ω ≠ 0) (a b : ℕ) :
    ω ^ a * (ω ^ b)⁻¹ = ω ^ ((a : ℤ) - (b : ℤ)) := by
  rw [zpow_sub₀ hω]
  push_cast [zpow_natCast]
  ring

lemma pow_mul_inv_pow_pow (ω : ℂ) (a b k : ℕ) :
    ω ^ (a * k) * (ω⁻¹) ^ (b * k) = (ω ^ a * (ω ^ b)⁻¹) ^ k := by
  rw [mul_pow, ← pow_mul, ← inv_pow, ← pow_mul]

/-- Orthogonality of distinct rows: for `j ≠ l`, the geometric sum vanishes. -/
lemma sum_pow_eq_zero {N : ℕ} (hN : N ≠ 0) {j l : Fin N} (hjl : j ≠ l) :
    ∑ k ∈ Finset.range N, (omegaN N ^ (j : ℕ) * (omegaN N ^ (l : ℕ))⁻¹) ^ k = 0 := by
  have hprim : IsPrimitiveRoot (omegaN N) N := isPrimitiveRoot_omegaN hN
  have hz := pow_mul_inv_pow (omegaN N) (omegaN_ne_zero N) (j : ℕ) (l : ℕ)
  have hne : omegaN N ^ ((j : ℤ) - (l : ℤ)) ≠ 1 := by
    rw [Ne, hprim.zpow_eq_one_iff_dvd]
    intro hdvd
    have habs : |((j : ℤ) - (l : ℤ))| < (N : ℤ) := by
      have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
      have hl : (l : ℤ) < N := by exact_mod_cast l.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
      have hl0 : (0 : ℤ) ≤ (l : ℤ) := by positivity
      rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact hjl (Fin.ext (by omega))
  have hpow : (omegaN N ^ ((j : ℤ) - (l : ℤ))) ^ N = 1 := by
    rw [← zpow_natCast (omegaN N ^ ((j : ℤ) - (l : ℤ))) N, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hprim.pow_eq_one, one_zpow]
  rw [hz, geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN : (2 ^ n : ℕ) ≠ 0 := by positivity
  set N := 2 ^ n with hNdef
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : Fin N, qft n j k * (star (qft n)) k l
      = (omegaN N ^ (j : ℕ) * (omegaN N ^ (l : ℕ))⁻¹) ^ (k : ℕ) / (N : ℂ) := by
    intro k
    have hstar : (star (qft n)) k l = (starRingEnd ℂ) (qft n l k) := rfl
    rw [hstar]
    simp only [qft, dftMatrix, Matrix.of_apply]
    rw [map_div₀, map_pow, conj_omegaN, Complex.conj_ofReal, div_mul_div_comm,
      sqrt_mul_sqrt N, pow_mul_inv_pow_pow]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range
      (fun k => (omegaN N ^ (j : ℕ) * (omegaN N ^ (l : ℕ))⁻¹) ^ k) N]
  by_cases hjl : j = l
  · subst hjl
    have hone : ∀ k ∈ Finset.range N, (omegaN N ^ (j : ℕ) * (omegaN N ^ (j : ℕ))⁻¹) ^ k = 1 := by
      intro k _
      rw [mul_inv_cancel₀ (pow_ne_zero _ (omegaN_ne_zero N)), one_pow]
    rw [Finset.sum_congr rfl hone]
    simp [hNC]
  · rw [sum_pow_eq_zero hN hjl]
    simp [hjl]

end QC

