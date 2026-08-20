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
