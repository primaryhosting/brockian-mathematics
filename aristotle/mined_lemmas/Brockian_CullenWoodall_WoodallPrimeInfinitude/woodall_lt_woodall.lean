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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

lemma woodall_lt_woodall {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) : woodall m < woodall n := by
  have hpow : (2 : ℕ) ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn.le
  have h1 : m * 2 ^ m < n * 2 ^ n :=
    lt_of_lt_of_le (by
        have : (0 : ℕ) < 2 ^ m := Nat.two_pow_pos m
        exact Nat.mul_lt_mul_of_lt_of_le hmn (le_refl _) this)
      (Nat.mul_le_mul_left n hpow)
  have hm1 : 1 ≤ m * 2 ^ m := one_le_mul_two_pow hm
  simp only [woodall]
  omega

