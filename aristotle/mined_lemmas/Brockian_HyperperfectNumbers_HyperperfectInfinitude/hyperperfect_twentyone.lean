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

theorem hyperperfect_twentyOne : Hyperperfect 21 := by
  have h := hyperperfect_mul_of_prime (p := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `301` is `6`-hyperperfect. -/
