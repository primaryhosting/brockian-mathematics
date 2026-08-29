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

A number `n > 1` is *`k`-hyperperfect* when `n = 1 + k * (σ(n) - n - 1)`, and
*hyperperfect* when it is `k`-hyperperfect for some `k ≥ 1` (the case `k = 1` is exactly
perfection).  Whether there are infinitely many hyperperfect numbers is open.

This file gives a Lean-checked conditional reduction: `HyperperfectInfinitude` shows that
the infinitude of the prime family `{p prime : p² - p + 1 prime}` implies the infinitude of
hyperperfect numbers, via the construction `p * (p² - p + 1)`, which is `(p-1)`-hyperperfect.
Unconditional instances `6, 21, 301, 2041` are recorded at the end.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number `n > 1` is *hyperperfect* if it is `k`-hyperperfect for some
`k ≥ 1`, i.e. `n = 1 + k * (σ(n) - n - 1)`.  We phrase the defining equation in a
subtraction-free way as `k * σ(n) + 1 = (k + 1) * n + k`; see
`hyperperfect_iff` for the equivalence with the usual formulation. -/
