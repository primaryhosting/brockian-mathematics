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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/

theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

/-- **Conditional reduction for the same-parity betrothed number problem.**

Whether a betrothed (quasi-amicable) pair of the same parity exists is an open problem;
all known betrothed pairs consist of one even and one odd number.  What is proved here is
a reduction: such a pair exists if and only if one exists in which *both* members are a
perfect square or twice a perfect square. -/
