import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8, mul_comm, mul_assoc, mul_left_comm] using this

lemma zeta8_pow_eight : zeta8 ^ (8 : ℕ) = 1 := isPrimitiveRoot_zeta8.pow_eq_one

lemma zeta8_ne_zero : zeta8 ≠ 0 := isPrimitiveRoot_zeta8.ne_zero (by norm_num)

lemma zeta8_pow_eq_one_iff (n : ℕ) : zeta8 ^ n = 1 ↔ 8 ∣ n :=
  isPrimitiveRoot_zeta8.pow_eq_one_iff_dvd n

lemma conj_zeta8_pow (a : ℕ) :
    (starRingEnd ℂ) (zeta8 ^ a) = zeta8 ^ (7 * a) := by
  have hconj : (starRingEnd ℂ) zeta8 = zeta8⁻¹ := by
    have h1 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8)
        = -(2 * (Real.pi : ℂ) * Complex.I / 8) := by
      simp [map_div₀, Complex.conj_I]
      ring
    calc (starRingEnd ℂ) zeta8
        = Complex.exp ((starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8)) := by
          rw [zeta8, Complex.exp_conj]
      _ = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / 8)) := by rw [h1]
      _ = zeta8⁻¹ := by rw [Complex.exp_neg, zeta8]
  have hmul : zeta8 ^ a * zeta8 ^ (7 * a) = 1 := by
    rw [← pow_add]
    have h : a + 7 * a = 8 * a := by ring
    rw [h, pow_mul, zeta8_pow_eight, one_pow]
  rw [map_pow, hconj, inv_pow]
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hmul; exact hmul)).symm

/-- Geometric sums of nontrivial powers of `zeta8` vanish. -/
lemma sum_zeta8_pow (n : ℕ) (h : ¬ (8 ∣ n)) :
    ∑ m : Fin 8, (zeta8 ^ n) ^ (m : ℕ) = 0 := by
  have hx : zeta8 ^ n ≠ 1 := fun hc => h ((zeta8_pow_eq_one_iff n).1 hc)
  have hpow : (zeta8 ^ n) ^ (8 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta8_pow_eight, one_pow]
  rw [Fin.sum_univ_eq_sum_range (fun m => (zeta8 ^ n) ^ m) 8, geom_sum_eq hx, hpow]
  simp

/-- The 3-qubit quantum Fourier transform matrix, acting on `Fin 8` basis states. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => zeta8 ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt 8 : ℝ)

lemma sqrt8_sq : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma sqrt8_ne_zero : ((Real.sqrt 8 : ℝ) : ℂ) ≠ 0 := by
  have h : Real.sqrt 8 ≠ 0 := by positivity
  simpa using h

/-- The 3-qubit QFT matrix is unitary. -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have hterm : ∀ m : Fin 8,
      (star qft3) j m * qft3 m k
        = (zeta8 ^ ((k : ℕ) + 7 * (j : ℕ))) ^ (m : ℕ) / 8 := by
    intro m
    have hpow : (zeta8 ^ ((k : ℕ) + 7 * (j : ℕ))) ^ (m : ℕ)
        = zeta8 ^ (7 * ((m : ℕ) * (j : ℕ))) * zeta8 ^ ((m : ℕ) * (k : ℕ)) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    have hs : (star qft3) j m
        = zeta8 ^ (7 * ((m : ℕ) * (j : ℕ))) / ((Real.sqrt 8 : ℝ) : ℂ) := by
      rw [Matrix.star_apply, Complex.star_def]
      show (starRingEnd ℂ) (zeta8 ^ ((m : ℕ) * (j : ℕ)) / ((Real.sqrt 8 : ℝ) : ℂ)) = _
      rw [map_div₀, conj_zeta8_pow, Complex.conj_ofReal]
    have hq : qft3 m k = zeta8 ^ ((m : ℕ) * (k : ℕ)) / ((Real.sqrt 8 : ℝ) : ℂ) := rfl
    rw [hs, hq, div_mul_div_comm, sqrt8_sq, hpow]
  simp only [Matrix.mul_apply, hterm, ← Finset.sum_div]
  by_cases hjk : j = k
  · subst hjk
    have hval : (j : ℕ) + 7 * (j : ℕ) = 8 * (j : ℕ) := by ring
    have h1 : zeta8 ^ ((j : ℕ) + 7 * (j : ℕ)) = 1 := by
      rw [hval, pow_mul, zeta8_pow_eight, one_pow]
    rw [h1]
    simp
  · have hnd : ¬ (8 ∣ ((k : ℕ) + 7 * (j : ℕ))) := by
      intro hdvd
      apply hjk
      have hj := j.isLt
      have hk := k.isLt
      have : (j : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    rw [sum_zeta8_pow _ hnd]
    simp [Matrix.one_apply, hjk]

end QC

