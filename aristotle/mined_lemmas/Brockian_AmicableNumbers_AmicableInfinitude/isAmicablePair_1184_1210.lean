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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many amicable pairs is an open problem, so the main result here
is a Lean-checked *conditional reduction*: the infinitude of amicable numbers follows from the
infinitude of the indices at which the three Thabit numbers are simultaneously prime.
Along the way Thabit ibn Qurra's rule is proved unconditionally, together with the classical
amicable pairs `(220, 284)` and `(1184, 1210)`.
-/

set_option maxRecDepth 100000

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem isAmicablePair_1184_1210 : IsAmicablePair 1184 1210 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold sigmaOne; decide

/-- `σ₁` is multiplicative on coprime arguments. -/
