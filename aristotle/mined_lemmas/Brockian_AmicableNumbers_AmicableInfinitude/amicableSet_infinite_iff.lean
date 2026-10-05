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

/-- The sum of the proper divisors of `n` (all divisors of `n` other than `n` itself). -/

theorem amicableSet_infinite_iff :
    amicableSet.Infinite ↔ ∀ N : ℕ, ∃ n ∈ amicableSet, N < n := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hn'⟩ := hinf.exists_gt N
    exact ⟨n, hn, hn'⟩
  · exact Set.infinite_of_forall_exists_gt

/-! ## Sum-of-divisors preliminaries -/

/-- `σ₁ n`, the sum of all divisors of `n`. -/
