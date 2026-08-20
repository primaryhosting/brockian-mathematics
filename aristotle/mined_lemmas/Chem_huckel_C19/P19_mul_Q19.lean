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

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma P19_mul_Q19 : P19 * Q19 = (19 : ℂ) • (1 : Matrix (Fin 19) (Fin 19) ℂ) := by
  ext j l
  rw [Matrix.mul_apply]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = zeta19 ^ j.val * (zeta19⁻¹) ^ l.val := ⟨_, rfl⟩
  have hterm : ∀ k : Fin 19, P19 j k * Q19 k l = z ^ k.val := by
    intro k
    simp only [P19, Q19, Matrix.of_apply, hz, mul_pow, ← pow_mul]
    rw [mul_comm k.val l.val]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 19]
  by_cases hjl : j = l
  · subst hjl
    have hz1 : z = 1 := by
      rw [hz, ← mul_pow, mul_inv_cancel₀ zeta19_ne_zero, one_pow]
    simp [hz1]
  · have hzne : z ≠ 1 := by
      intro h
      apply hjl
      have h' : zeta19 ^ j.val = zeta19 ^ l.val := by
        rw [hz, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ zeta19_ne_zero)] at h
        exact h
      exact Fin.ext (isPrimitiveRoot_zeta19.pow_inj j.isLt l.isLt h')
    have hz19 : z ^ 19 = 1 := by
      rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm j.val 19, mul_comm l.val 19,
        pow_mul, pow_mul, zeta19_pow_19, inv_pow, zeta19_pow_19]
      simp
    rw [geom_sum_19 hz19 hzne]
    simp [hjl]

