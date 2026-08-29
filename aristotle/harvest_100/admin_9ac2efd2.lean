/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The `n`-dimensional Quantum Fourier Transform matrix:
`(QFT n) j k = n^(-1/2) * exp (2 π i j k / n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ((Real.sqrt n)⁻¹ : ℝ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val * k.val : ℕ) : ℂ) / (n : ℂ))

/-- The primitive `n`-th root of unity used by the QFT. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := by
  have := Complex.isPrimitiveRoot_exp n hn
  simpa [zeta] using this

lemma norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  have h : zeta n = Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma qftMatrix_apply (n : ℕ) (j k : Fin n) :
    qftMatrix n j k = ((Real.sqrt n)⁻¹ : ℝ) * (zeta n) ^ (j.val * k.val) := by
  rw [qftMatrix, zeta]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The key orthogonality relation: the columns of the QFT matrix are orthonormal. -/
lemma qft_col_orthonormal {n : ℕ} (hn : n ≠ 0) (j l : Fin n) :
    ∑ k : Fin n, (starRingEnd ℂ) (qftMatrix n k j) * qftMatrix n k l
      = if j = l then 1 else 0 := by
  set z := zeta n with hz
  have hz0 : z ≠ 0 := zeta_ne_zero n
  have hprim : IsPrimitiveRoot z n := isPrimitiveRoot_zeta hn
  have hconj : (starRingEnd ℂ) z = z⁻¹ := (Complex.inv_eq_conj (norm_zeta n)).symm
  set s : ℝ := (Real.sqrt n)⁻¹ with hs
  have key : ∀ a b : ℕ, z ^ ((b : ℤ) - (a : ℤ)) = (z⁻¹) ^ a * z ^ b := by
    intro a b
    rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv, mul_comm]
  have e1 : ∀ k : Fin n, (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ (k.val)
      = (z⁻¹) ^ (k.val * j.val) * z ^ (k.val * l.val) := by
    intro k
    rw [← key, ← zpow_natCast (z ^ ((l.val : ℤ) - (j.val : ℤ))) k.val, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ k : Fin n,
      (starRingEnd ℂ) (qftMatrix n k j) * qftMatrix n k l
        = ((s : ℂ) ^ 2) * (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ (k.val) := by
    intro k
    rw [qftMatrix_apply, qftMatrix_apply, map_mul, map_pow, hconj, Complex.conj_ofReal, e1 k]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hsum : ∑ k : Fin n, (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ (k.val)
      = ∑ k ∈ Finset.range n, (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ k :=
    (Finset.sum_range fun k => (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ k).symm
  rw [hsum]
  have hs2 : ((s : ℂ)) ^ 2 = ((n : ℂ))⁻¹ := by
    have hnn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hreal : (s : ℝ) ^ 2 = ((n : ℝ))⁻¹ := by
      rw [hs, inv_pow, Real.sq_sqrt hnn]
    calc ((s : ℂ)) ^ 2 = (((s ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      _ = ((((n : ℝ))⁻¹ : ℝ) : ℂ) := by rw [hreal]
      _ = ((n : ℂ))⁻¹ := by push_cast; ring
  by_cases hjl : j = l
  · subst hjl
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, hs2, if_pos]
    exact inv_mul_cancel₀ (by exact_mod_cast hn)
  · have hj := j.isLt
    have hl := l.isLt
    have hne : (z ^ ((l.val : ℤ) - (j.val : ℤ))) ≠ 1 := by
      intro h
      rw [hprim.zpow_eq_one_iff_dvd] at h
      have habs : |(l.val : ℤ) - (j.val : ℤ)| < (n : ℤ) := by
        rw [abs_lt]
        omega
      have h0 := Int.eq_zero_of_abs_lt_dvd h habs
      exact hjl (Fin.ext (by omega))
    rw [geom_sum_eq hne]
    have hpow : (z ^ ((l.val : ℤ) - (j.val : ℤ))) ^ n = 1 := by
      rw [← zpow_natCast (z ^ ((l.val : ℤ) - (j.val : ℤ))) n, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [hpow, if_neg hjl]
    simp

/-- **The 5-qubit QFT matrix is unitary.** -/
theorem qft_unitary_5 : qftMatrix 32 ∈ Matrix.unitaryGroup (Fin 32) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  exact qft_col_orthonormal (by norm_num) j l

end QC

