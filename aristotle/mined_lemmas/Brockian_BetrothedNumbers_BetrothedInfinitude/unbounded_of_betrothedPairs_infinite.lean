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

/-- The sum-of-divisors function `σ₁`. -/

theorem unbounded_of_betrothedPairs_infinite (h : betrothedPairs.Infinite) :
    ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n := by
  intro N
  by_contra hc
  push_neg at hc
  have hsub : betrothedPairs ⊆ (fun m => (m, partner m)) '' Set.Iic N := by
    rintro ⟨m, n⟩ hp
    have hn : n = partner m := partner_eq_of_isBetrothedPair hp
    have hle : m ≤ N := by
      by_contra hlt
      exact hc m n (lt_of_not_ge hlt) hp
    exact ⟨m, hle, by simp [hn]⟩
  exact h (((Set.finite_Iic N).image _).subset hsub)

/-- The conjecture is equivalent to the unboundedness statement. -/
