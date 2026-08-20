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

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

/-- The number of primes strictly between `a` and `b`. -/

theorem three_le_nth_prime {n : ℕ} (hn : 1 ≤ n) : 3 ≤ Nat.nth Nat.Prime n := by
  rw [← nth_prime_one]
  exact Nat.nth_monotone Nat.infinite_setOf_prime hn

/-- Consecutive primes from `3` on differ by at least `2`. -/
