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

lemma sigma1_four_mul_seven_pow_ge {b : ℕ} (hb : 1 ≤ b) : 8 * 7 ^ b ≤ sigma1 (4 * 7 ^ b) := by
  have h := sigma1_mul_prime_pow (n := 4) (p := 7) (by norm_num) (by decide) b
  rw [sigma1_four] at h
  have hg := geom_seven b
  have h7 : (7 : ℕ) ^ (b + 1) = 7 * 7 ^ b := by ring
  have h1 : (7 : ℕ) ≤ 7 ^ b := by
    calc (7 : ℕ) = 7 ^ 1 := (pow_one 7).symm
      _ ≤ 7 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  omega

/-! ## Practicality of the two shapes -/

