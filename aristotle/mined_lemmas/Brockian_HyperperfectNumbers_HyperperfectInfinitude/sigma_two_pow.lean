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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of all divisors of `n`. -/

lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : sigma (2 ^ k) = ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
    simpa [sigma] using
      (Nat.sum_divisors_prime_pow (p := 2) (k := k) (f := fun d => d) Nat.prime_two)
  rw [h]
  clear h
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [pow_succ] at ih ⊢
      omega

/-- If `q = 2 ^ (k+1) - 1` is prime, then the even perfect number `2 ^ k * q` is
`1`-hyperperfect. -/
