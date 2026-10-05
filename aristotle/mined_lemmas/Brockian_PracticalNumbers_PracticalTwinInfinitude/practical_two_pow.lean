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

lemma practical_two_pow (a : ℕ) : Practical (2 ^ a) := by
  induction a with
  | zero => simpa using practical_one
  | succ a ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 2 ^ a ≤ ∑ y ∈ (2 ^ a : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    have h := practical_mul ih (d := 2) (by norm_num) (by omega)
    rwa [show 2 ^ a * 2 = 2 ^ (a + 1) by ring] at h

