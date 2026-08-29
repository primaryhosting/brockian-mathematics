/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

open Complex Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def qftOmega (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)

/-- The `n`-point discrete Fourier transform (quantum Fourier transform) matrix:
`F j k = n^(-1/2) * exp (2 π i j k / n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => ((Real.sqrt n : ℝ) : ℂ)⁻¹ * qftOmega n ^ (j.val * k.val)

/-- The entries of `qftMatrix` in the familiar exponential form. -/
lemma qftMatrix_apply (n : ℕ) (j k : Fin n) :
    qftMatrix n j k =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val) / n) := by
  unfold qftMatrix qftOmega
  simp only [Matrix.of_apply]
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma qftOmega_pow_n (n : ℕ) (hn : n ≠ 0) : qftOmega n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

lemma qftOmega_pow_eq_one_iff (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    qftOmega n ^ m = 1 ↔ n ∣ m :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one_iff_dvd m

/-- Orthogonality relation for the roots of unity. -/
lemma sum_qftOmega_pow (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    ∑ l ∈ Finset.range n, qftOmega n ^ (l * m) = if n ∣ m then (n : ℂ) else 0 := by
  have hx : ∀ l : ℕ, qftOmega n ^ (l * m) = (qftOmega n ^ m) ^ l := by
    intro l; rw [← pow_mul, Nat.mul_comm]
  simp only [hx]
  by_cases h : n ∣ m
  · have h1 : qftOmega n ^ m = 1 := (qftOmega_pow_eq_one_iff n hn m).mpr h
    simp [h1, h]
  · have h1 : qftOmega n ^ m ≠ 1 := fun hc =>
      h ((qftOmega_pow_eq_one_iff n hn m).mp hc)
    have h2 : (qftOmega n ^ m) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, qftOmega_pow_n n hn, one_pow]
    rw [geom_sum_eq h1, h2]
    simp [h]

lemma conj_qftOmega_pow (n : ℕ) (hn : n ≠ 0) (a : ℕ) (b : ℕ) (hb : b ≤ n) :
    (starRingEnd ℂ) (qftOmega n ^ (a * b)) = qftOmega n ^ (a * (n - b)) := by
  have hconj : (starRingEnd ℂ) (qftOmega n) = (qftOmega n)⁻¹ := by
    unfold qftOmega
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  have hne : qftOmega n ≠ 0 := by
    unfold qftOmega; exact Complex.exp_ne_zero _
  rw [map_pow, hconj, inv_pow, eq_comm]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have : a * (n - b) + a * b = n * a := by
    have : n - b + b = n := Nat.sub_add_cancel hb
    calc a * (n - b) + a * b = a * (n - b + b) := by ring
      _ = a * n := by rw [this]
      _ = n * a := Nat.mul_comm _ _
  rw [this, pow_mul, qftOmega_pow_n n hn, one_pow]

lemma eq_of_dvd_lt_two_mul {n s : ℕ} (h0 : 0 < s) (h2 : s < 2 * n) (hd : n ∣ s) : s = n := by
  obtain ⟨t, rfl⟩ := hd
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at h0
    · exact h
  have ht2 : t < 2 := by
    by_contra hc
    push_neg at hc
    have : 2 * n ≤ n * t := by nlinarith
    omega
  have ht0 : t ≠ 0 := by rintro rfl; simp at h0
  have : t = 1 := by omega
  subst this
  simp

/-- The `n`-point QFT matrix is unitary. -/
lemma qftMatrix_conjTranspose_mul (n : ℕ) (hn : n ≠ 0) :
    (qftMatrix n)ᴴ * qftMatrix n = 1 := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hinv : (((Real.sqrt n : ℝ) : ℂ))⁻¹ * (((Real.sqrt n : ℝ) : ℂ))⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]
    norm_num
  ext j k
  have hj := j.isLt
  have hk := k.isLt
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin n,
      (qftMatrix n)ᴴ j l * qftMatrix n l k
        = (n : ℂ)⁻¹ * qftOmega n ^ (l.val * ((n - j.val) + k.val)) := by
    intro l
    simp only [Matrix.conjTranspose_apply, qftMatrix, Matrix.of_apply, Complex.star_def,
      map_mul, map_inv₀, Complex.conj_ofReal]
    rw [conj_qftOmega_pow n hn l.val j.val hj.le, Nat.mul_add, pow_add, ← hinv]
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun l => qftOmega n ^ (l * (n - j.val + k.val))) n,
    sum_qftOmega_pow n hn]
  by_cases hjk : j = k
  · subst hjk
    have hd : n ∣ (n - j.val + j.val) := by rw [Nat.sub_add_cancel hj.le]
    rw [if_pos hd, Matrix.one_apply_eq, inv_mul_cancel₀ hnC]
  · have hnd : ¬ n ∣ (n - j.val + k.val) := by
      intro hd
      have h0 : 0 < n - j.val + k.val := by omega
      have h2 : n - j.val + k.val < 2 * n := by omega
      have h3 := eq_of_dvd_lt_two_mul h0 h2 hd
      exact hjk (Fin.ext (by omega))
    rw [if_neg hnd, Matrix.one_apply_ne hjk, mul_zero]

/-- **The 5-qubit QFT matrix (of size `2^5 = 32`) is unitary.** -/
theorem qft_unitary_5 : qftMatrix 32 ∈ Matrix.unitaryGroup (Fin 32) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qftMatrix_conjTranspose_mul 32 (by norm_num))

end QC

#print axioms QC.qft_unitary_5

