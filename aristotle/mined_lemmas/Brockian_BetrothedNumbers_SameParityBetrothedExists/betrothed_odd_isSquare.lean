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

theorem betrothed_odd_isSquare {m n : ℕ} (h : Betrothed m n) (hm : Odd m) (hn : Odd n) :
    IsSquare m ∧ IsSquare n := by
  have hpar : m % 2 = n % 2 := by
    rw [Nat.odd_iff] at hm hn; omega
  obtain ⟨h1, h2⟩ := sameParity_betrothed_structure h hpar
  constructor
  · rcases h1 with h1 | ⟨k, rfl⟩
    · exact h1
    · exact absurd hm (by simp [Nat.odd_iff, Nat.mul_mod_right])
  · rcases h2 with h2 | ⟨k, rfl⟩
    · exact h2
    · exact absurd hn (by simp [Nat.odd_iff, Nat.mul_mod_right])

/-- **Reduction for the existence of a same-parity betrothed pair.**

Whether a betrothed (quasi-amicable) pair whose two members have the same parity exists is an
open problem: all known betrothed pairs consist of one even and one odd number.  The theorem
below is a Lean-checked *reduction*: such a pair exists if and only if there is a betrothed
pair one of whose members is a square or twice a square.  (The two directions come from the
fact that `σ k` is odd exactly for `k` a square or twice a square, together with
`σ m = m + n + 1` for a betrothed pair.) -/
