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

theorem betrothedSmallerSet_infinite
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n) :
    betrothedSmallerSet.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨m, n, ham, hmn⟩ := h a
  exact ⟨m, ((isBetrothedPair_iff m n).1 hmn).1, ham⟩

/-- **Betrothed Infinitude (conditional reduction).**

If for every bound `N` there exists a betrothed (quasi-amicable) pair `(m, n)` with `m > N`,
then there are infinitely many betrothed pairs. -/
