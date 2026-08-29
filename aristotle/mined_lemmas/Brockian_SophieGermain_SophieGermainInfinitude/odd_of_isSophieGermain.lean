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

-- # Sophie Germain Infinitude
-- Category: Brockian Conjecture
-- Target: Brockian.SophieGermain.SophieGermainInfinitude
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem odd_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (hne : p ≠ 2) : Odd p :=
  hp.1.odd_of_ne_two hne

/-- Sophie Germain primes other than `2` and `3` are congruent to `2` mod `3`. -/
