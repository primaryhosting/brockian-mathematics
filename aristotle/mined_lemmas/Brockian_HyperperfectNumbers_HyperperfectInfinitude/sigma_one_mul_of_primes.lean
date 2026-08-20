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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, i.e. `k`
times the sum of the divisors of `n` other than `1` and `n` equals `n - 1`.
The equation is written without truncated subtraction as `n + k * (n + 1) = 1 + k * σ n`. -/

theorem sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hmul := (isMultiplicative_sigma (k := 1) :
      ArithmeticFunction.IsMultiplicative (σ 1 : ArithmeticFunction ℕ)).map_mul_of_coprime
      ((Nat.coprime_primes hp hq).mpr hpq)
  rw [hmul, sigma_one_apply, sigma_one_apply, hp.sum_divisors, hq.sum_divisors]

/-- **Key lemma.** If `p` and `q = p² - p + 1` are both prime, then `n = p * q` is
`(p-1)`-hyperperfect. (For `p = 2` this gives the perfect number `6`, for `p = 3` the
`2`-hyperperfect number `21`, for `p = 7` the `6`-hyperperfect number `301`.) -/
