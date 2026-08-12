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
noncomputable def qftRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point discrete Fourier transform (quantum Fourier transform) matrix:
`(QFT_N) j k = N^(-1/2) * exp (2πi j k / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ * (qftRoot N) ^ (j.val * k.val)

lemma qftRoot_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (qftRoot N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma qftRoot_ne_zero (N : ℕ) : qftRoot N ≠ 0 := Complex.exp_ne_zero _

lemma conj_qftRoot (N : ℕ) : (starRingEnd ℂ) (qftRoot N) = (qftRoot N)⁻¹ := by
  rw [qftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff, neg_div]

/-- Orthogonality of the columns of the DFT matrix. -/
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

private lemma inv_pow_mul_pow (z : ℂ) (a b c : ℕ) :
    (z⁻¹) ^ (a * b) * z ^ (a * c) = (z ^ c * (z ^ b)⁻¹) ^ a := by
  rw [inv_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm c a, mul_comm b a, mul_comm]

/-- The `N`-point QFT matrix is unitary, for any `N ≠ 0`. -/
theorem qftMatrix_mem_unitaryGroup {N : ℕ} (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have hc : star ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  have hsq : ((Real.sqrt N : ℂ)⁻¹) * ((Real.sqrt N : ℂ)⁻¹) = ((N : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]
  have key : ∀ k : Fin N, (star (qftMatrix N)) j k * qftMatrix N k l
      = ((N : ℂ))⁻¹ * ((qftRoot N) ^ (l.val) * ((qftRoot N) ^ (j.val))⁻¹) ^ (k.val) := by
    intro k
    rw [Matrix.star_apply]
    simp only [qftMatrix]
    rw [star_mul', hc, star_pow, Complex.star_def, conj_qftRoot]
    rw [← hsq]
    rw [show (Real.sqrt N : ℂ)⁻¹ * (qftRoot N)⁻¹ ^ (k.val * j.val) *
        ((Real.sqrt N : ℂ)⁻¹ * qftRoot N ^ (k.val * l.val))
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) *
          ((qftRoot N)⁻¹ ^ (k.val * j.val) * qftRoot N ^ (k.val * l.val)) from by ring]
    rw [inv_pow_mul_pow]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, qft_geom_sum hN j l]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl, inv_mul_cancel₀ (by exact_mod_cast hN), Matrix.one_apply_eq]
  · rw [if_neg h, mul_zero, Matrix.one_apply_ne h]

/-- **The 5-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_5 : qftMatrix (2 ^ 5) ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qftMatrix_mem_unitaryGroup (by norm_num)

end QC

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

