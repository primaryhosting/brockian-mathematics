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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- `sigmaOne n` is the sum of all positive divisors of `n`. -/

theorem no_betrothed_below_48 : ∀ m n : ℕ, m < 48 → ¬ IsBetrothed m n := by
  intro m n hm hb
  have hn : n = betrothedPartner m := (isBetrothed_iff.mp hb).2.2.2.1.symm
  subst hn
  revert hb
  interval_cases m <;> decide

/-- **Betrothed Infinitude.**  The set of betrothed (quasi-amicable) pairs is infinite if and
only if betrothed pairs occur with arbitrarily large first member.  Whether either side holds
is an open problem; this is the Lean-checked reduction between the two formulations. -/
