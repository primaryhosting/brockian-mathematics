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

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each one's
sum of divisors equals `m + n + 1`. -/

def SquareOrTwiceSquare (n : ℕ) : Prop :=
  ∃ a : ℕ, n = a ^ 2 ∨ n = 2 * a ^ 2

/-- Parity of a geometric-type sum with odd ratio. -/
