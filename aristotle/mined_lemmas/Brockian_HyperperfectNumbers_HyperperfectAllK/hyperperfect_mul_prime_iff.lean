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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one more than
`k` times the sum of its proper divisors other than `1`.  For `k = 1` this is exactly the
condition of being a perfect number. -/

theorem hyperperfect_mul_prime_iff {k p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Hyperperfect k (p * q) ↔ ((p : ℤ) - k) * ((q : ℤ) - k) = (k : ℤ) ^ 2 + 1 := by
  have h := hyperperfect_primePow_mul_prime_iff (k := k) (t := 1) hp hq hpq
  have hS : (sigmaPrimePow p 1 : ℤ) = 1 + (p : ℤ) := by
    simp [sigmaPrimePow, Finset.sum_range_succ]
  rw [pow_one] at h
  rw [h, hS]
  constructor <;> intro hh <;> linear_combination hh

/-- The statement of the conjecture: for every `k ≥ 1` there is a `k`-hyperperfect number. -/
