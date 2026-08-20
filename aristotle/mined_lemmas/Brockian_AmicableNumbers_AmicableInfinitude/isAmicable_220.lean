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

Whether there are infinitely many amicable numbers is a well-known open problem.
This file gives a Lean-checked **conditional reduction**: if there are infinitely many
Thābit-type exponents `k` (i.e. `3·2^k - 1`, `3·2^(k+1) - 1` and `9·2^(2k+1) - 1` are all
prime), then there are infinitely many amicable numbers.  It also records the
unconditional partial result that amicable numbers exist (the pair `(220, 284)`).
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction

/-- The sum of the proper divisors of `n`. -/

theorem isAmicable_220 : IsAmicable 220 := ⟨284, isAmicablePair_220_284⟩

/-- Thābit's rule is non-vacuous: at `k = 1` it produces the pair `(220, 284)`. -/
