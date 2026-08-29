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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

lemma geom_sum_mul_pred_le (p k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1) ≤ p ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : (∑ i ∈ Finset.range (k + 1 + 1), p ^ i)
        = (∑ i ∈ Finset.range (k + 1), p ^ i) + p ^ (k + 1) := Finset.sum_range_succ _ _
    have e2 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ p (k + 1)
    have h3 : p ^ (k + 1) * (p - 1) ≤ p ^ (k + 1) * p - p ^ (k + 1) := by
      cases p with
      | zero => omega
      | succ q => rw [Nat.mul_sub]; simp
    have hpk : p ^ (k + 1) ≤ p ^ (k + 1) * p := Nat.le_mul_of_pos_right _ hp
    rw [e1, e2, add_mul]
    omega

/-- The key multiplicative estimate: `σ(n) * ∏_{p ∣ n} (p - 1) ≤ n * ∏_{p ∣ n} p`,
which is the integral form of `σ(n) / n < ∏_{p ∣ n} p / (p - 1)`. -/
