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

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th base-ten repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1)`, i.e. the natural number
whose decimal expansion consists of `n` ones. -/

theorem repunit_succ' (n : ℕ) : repunit (n + 1) = 10 * repunit n + 1 := by
  have h := nine_mul_repunit_add_one n
  rw [repunit_succ]
  omega

/-- The decimal expansion of `repunit n` is a string of `n` ones. -/
