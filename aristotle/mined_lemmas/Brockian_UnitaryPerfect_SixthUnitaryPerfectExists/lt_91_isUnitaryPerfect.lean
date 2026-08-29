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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

theorem lt_91_isUnitaryPerfect {n : ℕ} (hn : n < 91) (h : IsUnitaryPerfect n) :
    n = 6 ∨ n = 60 ∨ n = 90 := by
  have key : ∀ m ∈ Finset.range 91, IsUnitaryPerfect m → m = 6 ∨ m = 60 ∨ m = 90 := by decide
  exact key n (Finset.mem_range.mpr hn) h

/-- **Conditional reduction for the sixth unitary perfect number.**

Whether a unitary perfect number other than the five known ones exists is open.
This theorem is a Lean-checked reduction: such a "sixth" unitary perfect number exists
if and only if there is a unitary perfect number outside the known list that is even,
exceeds `90`, has at least three distinct prime factors, and whose number of distinct
prime factors is at most `v₂(n) + 2`. -/
