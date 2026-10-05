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

def GoodPrimes : Set ℕ := {p : ℕ | p.Prime ∧ Nat.Prime (p * p + 1 - p)}

/-- **Hyperperfect Infinitude (conditional reduction).**
If there are infinitely many primes `p` such that `p² - p + 1` is also prime, then there
are infinitely many hyperperfect numbers.  Each such `p` yields the `(p-1)`-hyperperfect
number `p (p² - p + 1)`; e.g. `p = 2, 3, 7, 13` give `6, 21, 301, 2041`. -/
