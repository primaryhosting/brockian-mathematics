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
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Brockian

/-- The list of all primes below the wheel window `2 * 631 = 1262`. -/

theorem wheelPrimes631_covers :
    ∀ k ∈ Finset.Icc 2 631, ∃ p ∈ wheelPrimes631, 2 * p ≤ 2 * k ∧ (2 * k - p) ∈ wheelPrimes631 := by
  decide

/-- **Goldbach wheel, K = 2, modulus 631.** Every even number `n` with `4 ≤ n ≤ 2 * 631`
is a sum of two primes `p + q` with `p ≤ q`. -/
