import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

theorem sum_amp_sq {n : ℕ} (f : (Fin n → Bool) → Bool) : ∑ y, (amp f y) ^ 2 = 1 := by
  have hsq : ∀ y : Fin n → Bool, (amp f y) ^ 2
      = (1 / 2 ^ n : ℝ) ^ 2 * ∑ x, ∑ x', (sign (f x) * sign (f x')) * (phase x y * phase x' y) := by
    intro y
    unfold amp
    rw [mul_pow]
    congr 1
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  simp_rw [hsq]
  rw [← Finset.mul_sum]
  have hswap : (∑ y : Fin n → Bool, ∑ x, ∑ x',
        (sign (f x) * sign (f x')) * (phase x y * phase x' y))
      = ∑ x, ∑ x', (sign (f x) * sign (f x')) * ∑ y, (phase x y * phase x' y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x' _ => by rw [Finset.mul_sum]
  rw [hswap]
  simp_rw [phase_orthogonality, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    sign_sq_eq_one, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  rw [hc]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

end QI

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

