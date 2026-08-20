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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

def SixthUnitaryPerfectExistsStatement : Prop :=
  ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect

/-- **Conditional reduction for the sixth unitary perfect number.**
The existence of a unitary perfect number besides the five known ones is equivalent to the
existence of such a number that is moreover even and not a prime power.  In other words, the
search for a sixth unitary perfect number may be restricted to even numbers with at least two
distinct prime factors.  (Whether a sixth unitary perfect number exists is an open problem, so
the statement itself is not proved here; what is proved is this reduction.) -/
