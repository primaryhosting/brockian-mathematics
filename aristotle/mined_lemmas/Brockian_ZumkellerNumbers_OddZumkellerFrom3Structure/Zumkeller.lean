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

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is *Zumkeller* if it is positive and its set of divisors can be
split into two parts with equal sums. -/

def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- Sanity check: `6` is a Zumkeller number, via the split `{1, 2, 3} ∪ {6}`. -/
example : Zumkeller 6 := ⟨by norm_num, {1, 2, 3}, by decide, by decide⟩

/-- Sanity check: `945`, the smallest odd Zumkeller number, is Zumkeller,
via the split `{15, 945} ∪ (rest)`. -/
example : Zumkeller 945 := ⟨by norm_num, {15, 945}, by decide +kernel, by decide +kernel⟩

/-- A Zumkeller number is perfect or abundant: `2 * n ≤ σ n`. -/
