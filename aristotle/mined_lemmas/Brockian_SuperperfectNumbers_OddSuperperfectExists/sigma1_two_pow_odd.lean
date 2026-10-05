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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma sigma1_two_pow_odd (e : ℕ) : Odd (sigma1 (2 ^ e)) := by
  rw [Nat.odd_iff, sigma1_primePow Nat.prime_two, Finset.sum_range_succ']
  have h : 2 ∣ ∑ i ∈ range e, 2 ^ (i + 1) :=
    Finset.dvd_sum fun i _ => dvd_pow_self 2 (Nat.succ_ne_zero i)
  omega

/-- For an odd prime `p` and an even exponent `e`, `σ(p^e)` is odd. -/
