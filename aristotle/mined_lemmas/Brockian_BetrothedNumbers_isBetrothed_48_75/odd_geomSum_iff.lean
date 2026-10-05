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

theorem odd_geomSum_iff {p k : ℕ} (hp : p.Prime) :
    Odd (∑ i ∈ range (k + 1), p ^ i) ↔ (p = 2 ∨ Even k) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · simpa [Nat.odd_iff] using geomSum_two_mod_two k
  · have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rw [Nat.odd_iff, geomSum_mod_two_of_odd hpo]
    simp only [hp2, false_or, Nat.even_iff]
    omega

/-- A positive natural number all of whose prime exponents are even is a square. -/
