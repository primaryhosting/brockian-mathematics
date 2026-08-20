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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.HyperperfectNumbers

open scoped BigOperators

/-- `n` is `k`-hyperperfect if `n > 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` is one plus
`k` times the sum of the divisors of `n` other than `1` and `n`. -/

lemma sigma_one_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ArithmeticFunction.sigma 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    hp.sum_divisors, hq.sum_divisors]

/-- Characterisation of `k`-hyperperfectness for a product of two distinct primes. -/
