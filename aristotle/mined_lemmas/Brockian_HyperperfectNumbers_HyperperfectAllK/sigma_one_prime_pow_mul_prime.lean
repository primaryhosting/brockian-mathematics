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

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

lemma sigma_one_prime_pow_mul_prime {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigma 1 (p ^ a * q) = (∑ i ∈ Finset.range (a + 1), p ^ i) * (q + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).2 hne)),
    sigma_one_prime_pow hp, sigma_one_prime hq]

/-! ### A construction of hyperperfect numbers -/

/-- A *witness* for `k`: a prime power times a prime, `n = p ^ a * q`, satisfying the
hyperperfection equation `k * σ n + 1 = (k + 1) * n + k`. -/
