import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Brockian

/-- The list of all primes not exceeding the wheel modulus `947`. -/

theorem exists_pair_primesUpTo947 :
    ∀ n ∈ List.range 474, n < 2 ∨ ∃ p ∈ primesUpTo947, ∃ q ∈ primesUpTo947, p + q = 2 * n := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even number `n` with `4 ≤ n ≤ 947` is a sum of two primes. -/
