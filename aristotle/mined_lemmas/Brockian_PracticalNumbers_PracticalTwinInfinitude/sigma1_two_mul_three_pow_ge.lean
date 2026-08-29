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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma sigma1_two_mul_three_pow_ge {a : ℕ} (ha : 1 ≤ a) : 4 * 3 ^ a ≤ sigma1 (2 * 3 ^ a) := by
  have h := sigma1_mul_prime_pow (n := 2) Nat.prime_three (by decide) a
  rw [sigma1_two] at h
  have hg := geom_three a
  have h3 : (3 : ℕ) ^ (a + 1) = 3 * 3 ^ a := by ring
  have h1 : (3 : ℕ) ≤ 3 ^ a := by
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

