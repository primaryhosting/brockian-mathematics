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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is a *Zumkeller number* if its set of divisors can be split into two
parts of equal sum, i.e. there is a set `S` of divisors of `n` whose sum is half of `σ(n)`. -/

lemma zumkeller_25515 : IsZumkeller 25515 := ⟨{15, 135, 567, 25515}, by decide, by decide⟩

/-- For every exponent `a ≥ 3`, the number `3 ^ a * 5 * 7` is a Zumkeller number. -/
