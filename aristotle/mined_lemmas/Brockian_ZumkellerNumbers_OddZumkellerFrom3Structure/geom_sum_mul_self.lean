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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/

theorem geom_sum_mul_self (p k : ℕ) :
    (∑ x ∈ Finset.range (k + 1), p ^ x) * p + 1
      = p ^ (k + 1) + ∑ x ∈ Finset.range (k + 1), p ^ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ (n := k + 1)]
    ring_nf
    ring_nf at ih
    omega

/-- For a prime `p` with `3 ≤ c ≤ p`, the divisor sum of `p ^ k` is smaller than
`c / (c - 1)` times `p ^ k`. -/
