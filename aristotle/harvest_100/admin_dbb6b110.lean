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
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := fun j k =>
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / ((2 : ℂ) ^ n)) /
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ)

/-- Complex conjugation of a QFT entry flips the sign of the phase. -/
lemma conj_qft_apply (n : ℕ) (m j : Fin (2 ^ n)) :
    (starRingEnd ℂ) (qft n m j)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) * (j : ℕ)) / ((2 : ℂ) ^ n))) /
        ((Real.sqrt (2 ^ n) : ℝ) : ℂ) := by
  simp only [qft, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_pow, map_ofNat, Complex.conj_I, Complex.conj_natCast,
    Complex.conj_ofReal]
  ring

/-- A nontrivial geometric sum of `N`-th roots of unity vanishes. -/
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
theorem qft_unitary_7 : qft 7 ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Matrix.one_apply, RCLike.star_def]
  exact qft_col_orthogonal 7 j k

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

