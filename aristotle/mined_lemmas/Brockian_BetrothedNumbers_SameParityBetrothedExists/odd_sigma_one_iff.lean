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

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- A *betrothed* (quasi-amicable) pair: two distinct positive numbers each of whose
sum of divisors equals `m + n + 1`. -/

theorem odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ (IsSquare n ∨ ∃ k, n = 2 * k ^ 2) := by
  rw [odd_sigma_one_iff_factorization hn, factorization_even_iff_two_pow_mul_sq hn]
  constructor
  · rintro ⟨a, k, rfl⟩
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      exact ⟨2 ^ b * k, by subst hb; ring⟩
    · right
      exact ⟨2 ^ b * k, by subst hb; ring⟩
  · rintro (⟨r, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨0, r, by ring⟩
    · exact ⟨1, k, by ring⟩

/-! ### Parity of betrothed pairs -/

/-- For a betrothed pair, the two members have the same parity iff `σ m` is odd. -/
