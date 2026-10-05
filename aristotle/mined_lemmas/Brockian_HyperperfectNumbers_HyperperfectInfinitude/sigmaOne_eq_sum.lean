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

lemma sigmaOne_eq_sum (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  simp [sigmaOne, ArithmeticFunction.sigma_apply]

/-- A natural number `n` is **hyperperfect** if there is a positive integer `k` with
`n = 1 + k * (σ(n) - n - 1)`, where `σ` is the sum-of-divisors function.  (For `k = 1`
this is exactly the condition that `n` is a perfect number.)  The subtraction is
performed in `ℤ`, so no truncation occurs. -/
