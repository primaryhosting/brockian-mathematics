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

theorem isHyperperfect_one_iff_perfect (n : ℕ) : IsHyperperfect 1 n ↔ n.Perfect ∧ 1 < n := by
  rw [isHyperperfect_iff_properDivisors, Nat.Perfect]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, h1⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    omega

/-- The algebraic heart of the two-prime case: with `p = k + a` and `q = k + b`, the
hyperperfection identity for `p * q` is equivalent to `a * b = k ^ 2 + 1`. -/
