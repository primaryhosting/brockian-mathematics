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

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

theorem mul_sub_eq_iff (k a b : ℕ) :
    k * ((1 + (k + a)) * (1 + (k + b))) + 1 = (k + 1) * ((k + a) * (k + b)) + k ↔
      a * b = k ^ 2 + 1 := by
  constructor <;> intro h <;> nlinarith [h]

/-- Structure of hyperperfect numbers that are products of two distinct primes: `p * q` is
`k`-hyperperfect exactly when `(p - k) * (q - k) = k ^ 2 + 1`, both `p` and `q` exceeding `k`. -/
