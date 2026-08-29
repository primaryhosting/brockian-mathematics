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

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

theorem sigmaOne_eq_properDivisors_add (n : ℕ) :
    sigmaOne n = (∑ d ∈ n.properDivisors, d) + n := by
  rw [sigmaOne, ← Nat.sum_divisors_eq_sum_properDivisors_add_self]

/-! ## Reformulations -/

/-- Reformulation of `k`-hyperperfection in terms of the sum `s (n)` of the *proper* divisors of
`n`: the condition is `n = 1 + k * (s (n) - 1)`, written subtraction-free. -/
