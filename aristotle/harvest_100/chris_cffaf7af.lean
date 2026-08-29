import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)` used to build the QFT matrix. -/
noncomputable def qftOmega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point quantum Fourier transform matrix, `F j k = ω^(j*k) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ * qftOmega N ^ (j.val * k.val)

lemma qftOmega_ne_zero (N : ℕ) : qftOmega N ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_qftOmega {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (qftOmega N) N := by
  simpa [qftOmega] using Complex.isPrimitiveRoot_exp N hN

lemma conj_qftOmega (N : ℕ) :
    (starRingEnd ℂ) (qftOmega N) = (qftOmega N)⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.ext_iff]
  ring

/-- Geometric sum of powers of `ω^d` vanishes for `0 < d < N`. -/
lemma sum_qftOmega_pow_eq_zero {N d : ℕ} (hd : d ≠ 0) (hdN : d < N) :
    ∑ m ∈ Finset.range N, (qftOmega N ^ d) ^ m = 0 := by
  have hN : N ≠ 0 := by omega
  have hprim := isPrimitiveRoot_qftOmega hN
  have hne : qftOmega N ^ d ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hd hdN
  have hpow : (qftOmega N ^ d) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma sqrt_inv_mul_sqrt_inv (N : ℕ) :
    ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

lemma qft_conjTranspose_mul_self {N : ℕ} (hN : N ≠ 0) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have key : ∀ j k : Fin N, j.val ≤ k.val →
      ((qftMatrix N)ᴴ * qftMatrix N) j k = (1 : Matrix (Fin N) (Fin N) ℂ) j k := by
    intro j k hjk
    have hterm : ∀ m : Fin N,
        (qftMatrix N)ᴴ j m * qftMatrix N m k
          = (N : ℂ)⁻¹ * (qftOmega N ^ (k.val - j.val)) ^ m.val := by
      intro m
      simp only [Matrix.conjTranspose_apply, qftMatrix, star_mul', star_inv₀, star_pow,
        Complex.star_def, Complex.conj_ofReal, conj_qftOmega]
      have hsplit : qftOmega N ^ (m.val * k.val)
          = qftOmega N ^ (m.val * j.val) * (qftOmega N ^ (k.val - j.val)) ^ m.val := by
        rw [← pow_mul, ← pow_add]
        congr 1
        have h := Nat.sub_add_cancel hjk
        calc m.val * k.val = m.val * ((k.val - j.val) + j.val) := by rw [h]
          _ = m.val * j.val + (k.val - j.val) * m.val := by ring
      rw [hsplit, ← sqrt_inv_mul_sqrt_inv N]
      have h0 : qftOmega N ≠ 0 := qftOmega_ne_zero N
      have hinv : (qftOmega N)⁻¹ ^ (m.val * j.val) * qftOmega N ^ (m.val * j.val) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
      linear_combination ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ *
        (qftOmega N ^ (k.val - j.val)) ^ m.val) * hinv
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun m => (qftOmega N ^ (k.val - j.val)) ^ m)]
    rcases eq_or_lt_of_le hjk with h | h
    · have hjk' : j = k := Fin.ext h
      subst hjk'
      simp only [Nat.sub_self, pow_zero, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Matrix.one_apply_eq]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN)
    · have hd : k.val - j.val ≠ 0 := by omega
      have hdN : k.val - j.val < N := by omega
      rw [sum_qftOmega_pow_eq_zero hd hdN, mul_zero]
      have hne : j ≠ k := fun hc => by rw [hc] at h; omega
      rw [Matrix.one_apply_ne hne]
  ext j k
  rcases le_total j.val k.val with h | h
  · exact key j k h
  · have hherm : ((qftMatrix N)ᴴ * qftMatrix N)ᴴ = (qftMatrix N)ᴴ * qftMatrix N := by
      simp [Matrix.conjTranspose_mul]
    have hjk := congrArg (fun M => M j k) hherm
    simp only [Matrix.conjTranspose_apply] at hjk
    rw [← hjk, key k j h]
    rcases eq_or_ne k j with hkj | hkj
    · subst hkj; simp
    · rw [Matrix.one_apply_ne hkj, Matrix.one_apply_ne (Ne.symm hkj)]
      simp

/-- The 7-qubit QFT matrix (of size `2^7 = 128`) is unitary. -/
theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact qft_conjTranspose_mul_self (by norm_num)

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

