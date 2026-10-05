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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/

lemma geom_sum_succ (k j : ℕ) :
    k * (∑ i ∈ range (j + 1), (k + 1) ^ i) + 1 = (k + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, pow_succ ((k + 1)) (j + 1)]
      rw [← ih]
      ring

/-- **Construction of hyperperfect numbers.** If `q = k + 1` is prime and `p = q ^ (j+1) - k`
is prime (with `j ≥ 1`), then `q ^ j * p` is a `k`-hyperperfect number.

For `k = 1` this is the Euclid construction of even perfect numbers from Mersenne primes;
for `k = 2` it is the family `3 ^ j * (3 ^ (j+1) - 2)` (e.g. `21`, `2133`, ...). -/
