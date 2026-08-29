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

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/

lemma practical_two_mul_three_pow (b : ℕ) : Practical (2 * 3 ^ b) := by
  induction b with
  | zero =>
    have h := practical_mul practical_one (d := 2) (by norm_num) (by simp)
    simpa using h
  | succ b ih =>
    have h1 : (1 : ℕ) ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 * 3 ^ b ≤ ∑ y ∈ (2 * 3 ^ b : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    have h := practical_mul ih (d := 3) (by norm_num) (by omega)
    rwa [show 2 * 3 ^ b * 3 = 2 * 3 ^ (b + 1) by ring] at h

/-- Between `2 ^ a / 4` and `2 ^ a` there is always a power of `3`. -/
