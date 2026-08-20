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

theorem betrothed_symm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  exact ⟨hn, hm, hne.symm, by omega, by omega⟩

/-! ### Parity of the sum-of-divisors function -/

