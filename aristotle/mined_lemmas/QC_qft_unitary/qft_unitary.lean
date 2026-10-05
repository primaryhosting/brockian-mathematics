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

