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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

theorem sophieGermain_examples :
    ∀ p ∈ [2, 3, 5, 11, 23, 29, 41, 53, 83, 89], IsSophieGermainPrime p := by
  intro p hp
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

/-- **Conditional reduction of the Sophie Germain conjecture.**
If there are arbitrarily large primes `p` for which `2 * p + 1` divides `2 ^ p - 1` or
`2 ^ p + 1`, then there are infinitely many Sophie Germain primes. -/
