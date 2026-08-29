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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/

theorem le_of_mem_divisors {n y : ℕ} (hy : y ∈ n.divisors) : y ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hy).2) (Nat.mem_divisors.mp hy).1

/-- Main multiplication criterion: if the divisors of `n` reach `B`, with `n ≤ B`,
then `n * k` is practical for every `0 < k ≤ B + 1`. -/
