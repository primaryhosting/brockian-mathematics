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

theorem sameParity_betrothed_structure {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    (∃ a b : ℕ, 0 < b ∧ m = 2 ^ a * b ^ 2) ∧ (∃ a b : ℕ, 0 < b ∧ n = 2 ^ a * b ^ 2) := by
  obtain ⟨hm, hn⟩ := odd_sigma_of_sameParity h hpar
  exact ⟨eq_two_pow_mul_sq_of_odd_sigma h.1 hm, eq_two_pow_mul_sq_of_odd_sigma h.2.1 hn⟩

/-- A betrothed pair of two odd numbers would consist of two perfect squares. -/
