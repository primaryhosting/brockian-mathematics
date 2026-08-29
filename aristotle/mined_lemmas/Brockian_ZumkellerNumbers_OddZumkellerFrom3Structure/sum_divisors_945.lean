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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ZumkellerNumbers

open Finset

/-- A natural number `n` is a *Zumkeller number* if it is positive and its set of divisors
can be split into two parts of equal sum; equivalently, some set `S` of divisors of `n`
satisfies `2 * ∑ S = σ₁ n`. -/

lemma sum_divisors_945 : ∑ d ∈ (945 : ℕ).divisors, d = 1920 := by rfl

/-- `945 = 3^3 · 5 · 7`, the smallest odd Zumkeller number, is indeed Zumkeller:
the divisors `{15, 945}` sum to `960 = 1920 / 2`. -/
