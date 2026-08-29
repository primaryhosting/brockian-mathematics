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

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/

theorem geomSum_two_mod_two (k : ℕ) : (∑ i ∈ range (k + 1), 2 ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod]
    simp

/-- Parity of the geometric sum attached to a prime power. -/
