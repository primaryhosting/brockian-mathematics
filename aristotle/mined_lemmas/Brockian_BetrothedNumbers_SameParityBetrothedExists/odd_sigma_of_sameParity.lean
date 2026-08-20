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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose sum of divisors equals the sum of the two numbers plus one. -/

theorem odd_sigma_of_sameParity {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    Odd (sigma 1 m) ∧ Odd (sigma 1 n) := by
  obtain ⟨-, -, -, hm, hn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.odd_iff]; omega
  · rw [hn, Nat.odd_iff]; omega

/-- **Structure of a hypothetical same-parity betrothed pair.**
Both members of a betrothed pair of equal parity are of the form `2 ^ a * b ^ 2`. -/
