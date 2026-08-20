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

lemma sigma_one_primePow_mul_prime {p t q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p ^ t * q) = sigmaPrimePow p t * (q + 1) := by
  have hcop : Nat.Coprime (p ^ t) q :=
    Nat.Coprime.pow_left t ((Nat.coprime_primes hp hq).mpr hpq)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_primePow hp, sigma_one_prime hq]

/-- **Characterisation of hyperperfect numbers of the shape `p ^ t * q`.**
For distinct primes `p, q`, the number `p ^ t * q` is `k`-hyperperfect exactly when the
displayed Diophantine equation holds, where `S = 1 + p + ⋯ + p ^ t = σ (p ^ t)`. -/
