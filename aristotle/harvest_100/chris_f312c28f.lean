/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- A primitive 8-th root of unity, `exp (2πi/8)`. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix: an `8 × 8` matrix with entries
`(1/√8) * ζ^(j*k)` where `ζ = exp(2πi/8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * zeta8 ^ (j.val * k.val)

lemma zeta8_primitive : IsPrimitiveRoot zeta8 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8] using this

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := zeta8_primitive.pow_eq_one

lemma zeta8_pow_ne_one {d : ℕ} (hd : ¬ (8 ∣ d)) : zeta8 ^ d ≠ 1 := by
  intro h
  exact hd (zeta8_primitive.dvd_of_pow_eq_one d h)

lemma conj_zeta8 : (starRingEnd ℂ) zeta8 = zeta8⁻¹ := by
  have h : ‖zeta8‖ = 1 := by
    simp [zeta8, Complex.norm_exp]
  rw [← Complex.inv_eq_conj h]

lemma geom_sum_zeta8 {d : ℕ} (hd : ¬ (8 ∣ d)) :
    ∑ l ∈ Finset.range 8, (zeta8 ^ d) ^ l = 0 := by
  rw [geom_sum_eq (zeta8_pow_ne_one hd)]
  have : (zeta8 ^ d) ^ 8 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta8_pow_eight, one_pow]
  rw [this]
  simp

/-- Rows of `qft3` are orthonormal. -/
lemma qft3_row_inner (j k : Fin 8) :
    ∑ l : Fin 8, qft3 j l * (starRingEnd ℂ) (qft3 k l) = if j = k then 1 else 0 := by
  have hsq : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
    rw [← mul_inv]
    norm_cast
    rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  -- rewrite the summand
  have key : ∀ l : Fin 8,
      qft3 j l * (starRingEnd ℂ) (qft3 k l)
        = (8 : ℂ)⁻¹ * (zeta8 ^ (j.val + (8 - k.val))) ^ l.val := by
    intro l
    have hk : k.val ≤ 8 := le_of_lt k.isLt
    simp only [qft3, Matrix.of_apply, map_mul, map_pow, conj_zeta8, Complex.conj_ofReal,
      map_inv₀]
    have h1 : zeta8 ^ k.val * zeta8 ^ (8 - k.val) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
      exact zeta8_pow_eight
    have h2 : (zeta8 ^ k.val)⁻¹ = zeta8 ^ (8 - k.val) := inv_eq_of_mul_eq_one_right h1
    have hinv : (zeta8⁻¹) ^ (k.val * l.val) = (zeta8 ^ (8 - k.val)) ^ l.val := by
      rw [pow_mul, inv_pow, h2]
    calc (((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * zeta8 ^ (j.val * l.val)) *
        (((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * (zeta8⁻¹) ^ (k.val * l.val))
        = (((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹) *
          (zeta8 ^ (j.val * l.val) * (zeta8⁻¹) ^ (k.val * l.val)) := by ring
      _ = (8 : ℂ)⁻¹ * (zeta8 ^ (j.val + (8 - k.val))) ^ l.val := by
          rw [hsq, hinv, pow_add, mul_pow, pow_mul]
  rw [Finset.sum_congr rfl (fun l _ => key l), ← Finset.mul_sum]
  have hrange : ∑ l : Fin 8, (zeta8 ^ (j.val + (8 - k.val))) ^ l.val
      = ∑ l ∈ Finset.range 8, (zeta8 ^ (j.val + (8 - k.val))) ^ l := by
    rw [Finset.sum_range fun l => (zeta8 ^ (j.val + (8 - k.val))) ^ l]
  rw [hrange]
  by_cases hjk : j = k
  · subst hjk
    have hd : j.val + (8 - j.val) = 8 := by omega
    rw [hd, zeta8_pow_eight]
    simp
  · have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hd : ¬ (8 ∣ (j.val + (8 - k.val))) := by
      have hj := j.isLt
      have hk := k.isLt
      omega
    rw [geom_sum_zeta8 hd, if_neg hjk, mul_zero]

/-- The 3-qubit QFT matrix is unitary. -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Matrix.one_apply, Complex.star_def]
  rw [qft3_row_inner j k]

end QC

#print axioms QC.qft_unitary_3

