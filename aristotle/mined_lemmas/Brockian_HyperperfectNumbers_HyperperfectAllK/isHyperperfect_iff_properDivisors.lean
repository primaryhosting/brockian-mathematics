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

theorem isHyperperfect_iff_properDivisors (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ k * (∑ d ∈ n.properDivisors, d) + 1 = n + k := by
  rw [IsHyperperfect, sigmaOne_eq_properDivisors_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by nlinarith⟩

/-- For `k = 1` hyperperfection is exactly perfection. -/
