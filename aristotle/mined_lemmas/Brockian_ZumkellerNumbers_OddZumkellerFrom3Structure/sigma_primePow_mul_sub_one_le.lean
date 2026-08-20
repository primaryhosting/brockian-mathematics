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

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/

theorem sigma_primePow_mul_sub_one_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ d ∈ (p ^ k).divisors, d) * (p - 1) ≤ p ^ k * p := by
  rw [Nat.sum_divisors_prime_pow hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, add_mul]
      calc (∑ i ∈ Finset.range (k + 1), (q + 1) ^ i) * q + (q + 1) ^ (k + 1) * q
          ≤ (q + 1) ^ k * (q + 1) + (q + 1) ^ (k + 1) * q := Nat.add_le_add_right ih _
        _ = (q + 1) ^ (k + 1) * (q + 1) := by ring

/-- Key elementary bound: `σ₁ n / n ≤ ∏_{p ∣ n} p / (p-1)`, in a subtraction-free form. -/
