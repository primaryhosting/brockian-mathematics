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

namespace Brockian.ZumkellerNumbers

lemma geom_sum_lt_two_mul_pow (p k : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range (k + 1), p ^ i < 2 * p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * p ^ k ≤ p ^ (k + 1) := by
        have := Nat.mul_le_mul_right (p ^ k) hp
        simpa [pow_succ, Nat.mul_comm] using this
      rw [Finset.sum_range_succ]
      have : 2 * p ^ (k + 1) = p ^ (k + 1) + p ^ (k + 1) := by ring
      omega

/-- Prime powers are deficient: `σ (p ^ k) < 2 * p ^ k`. -/
