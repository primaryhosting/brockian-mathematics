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
