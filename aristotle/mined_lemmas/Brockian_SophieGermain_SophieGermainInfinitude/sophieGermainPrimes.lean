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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

def sophieGermainPrimes : Set ℕ := {p | IsSophieGermainPrime p}

example : IsSophieGermainPrime 2 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 3 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 5 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 11 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 23 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 29 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 41 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 53 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 83 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 89 := by norm_num [IsSophieGermainPrime]

/-- Unconditional structural result: every Sophie Germain prime `p > 3` satisfies
`p % 6 = 5`. -/
