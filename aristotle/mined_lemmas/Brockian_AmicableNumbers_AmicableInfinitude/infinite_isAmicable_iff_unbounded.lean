import Brockian.AmicableNumbers

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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- `a` and `b` form an *amicable pair*: they are distinct and each is the sum of the
proper divisors of the other, equivalently `σ₁ a = σ₁ b = a + b`. -/

theorem infinite_isAmicable_iff_unbounded :
    {a : ℕ | IsAmicable a}.Infinite ↔ ∀ N : ℕ, ∃ a, N < a ∧ IsAmicable a := by
  constructor
  · intro h N
    obtain ⟨a, ha, haN⟩ := h.exists_gt N
    exact ⟨a, haN, ha⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨a, haN, ha⟩ := h N
    exact ⟨a, ha, haN⟩

/-- **Conditional reduction of the amicable-number infinitude problem.**
If there are infinitely many parameters `m` satisfying the hypothesis of Euler's rule
(i.e. infinitely many `n = m + 2` for which `3·2^(n-1) - 1`, `3·2^n - 1` and `9·2^(2n-1) - 1`
are simultaneously prime), then there are infinitely many amicable numbers. -/
