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

lemma one_lt_of_odd_superperfect {n : ℕ} (hn : Odd n) (hs : Superperfect n) : 1 < n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp at hn
    · rw [Superperfect, sigma1_one, sigma1_one] at hs; omega
  · omega

/-- Any odd superperfect number `n` has `σ(n)` divisible by a prime congruent to `1` modulo `4`. -/
