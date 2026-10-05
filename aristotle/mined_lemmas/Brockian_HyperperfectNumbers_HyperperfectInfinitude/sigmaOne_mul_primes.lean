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

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of the divisors of `n`. -/

lemma sigmaOne_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigmaOne (p * q) = (p + 1) * (q + 1) := by
  rw [sigmaOne,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      ((Nat.coprime_primes hp hq).2 hne)]
  simp [ArithmeticFunction.sigma_apply, hp.sum_divisors, hq.sum_divisors]

/-! ## The basic infinite family

If `p` and `q = p² - p + 1` are both prime, then `n = p * q` is `(p-1)`-hyperperfect:
indeed `σ(n) - n - 1 = p + q = p² + 1` while `n - 1 = p³ - p² + p - 1 = (p-1)(p² + 1)`.
-/

