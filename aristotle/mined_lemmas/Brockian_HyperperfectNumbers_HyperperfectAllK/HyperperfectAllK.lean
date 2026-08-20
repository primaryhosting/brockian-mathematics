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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one more than
`k` times the sum of its proper divisors other than `1`.  For `k = 1` this is exactly the
condition of being a perfect number. -/

theorem HyperperfectAllK (H : PrimePowShapeSolvableForAllK) : HyperperfectExistsForAllK := by
  -- The unconditional statement `HyperperfectExistsForAllK` is not established here; what is
  -- proved is the reduction to the prime-pattern hypothesis `PrimePowShapeSolvableForAllK`,
  -- together with the explicit witnesses recorded in the `Examples` section below.
  intro k hk
  obtain ⟨p, t, q, hp, hq, hpq, heq⟩ := H k hk
  exact ⟨p ^ t * q, hyperperfect_of_primePow_mul_prime hp hq hpq heq⟩

section Examples

/-- `6` is `1`-hyperperfect (i.e. perfect). -/
