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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem knownUnitaryPerfect_isUnitaryPerfect :
    ∀ n ∈ knownUnitaryPerfect, IsUnitaryPerfect n := by
  intro n hn
  simp only [knownUnitaryPerfect, mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_big

/-! ### Structure of any unitary perfect number -/

/-- A unitary perfect number has at least two distinct prime factors. -/
