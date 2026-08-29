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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

lemma factorization_ne_zero_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    n.factorization p ≠ 0 := by
  rw [← Nat.support_factorization] at h
  exact Finsupp.mem_support_iff.mp h

/-- The only unitary perfect number with exactly two distinct prime factors is `6`. -/
