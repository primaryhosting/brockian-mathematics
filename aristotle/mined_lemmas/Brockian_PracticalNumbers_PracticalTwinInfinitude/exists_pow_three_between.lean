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

lemma exists_pow_three_between (a : ℕ) : ∃ b, 3 ^ b ≤ 2 ^ a ∧ 2 ^ a ≤ 4 * 3 ^ b := by
  induction a with
  | zero => exact ⟨0, by norm_num⟩
  | succ a ih =>
    obtain ⟨b, hb1, hb2⟩ := ih
    by_cases h : 2 ^ (a + 1) ≤ 4 * 3 ^ b
    · refine ⟨b, ?_, h⟩
      rw [pow_succ]; omega
    · refine ⟨b + 1, ?_, ?_⟩
      · rw [pow_succ, pow_succ]; omega
      · rw [pow_succ, pow_succ]; omega

/-- The key construction: for every `K` there is a practical `n > K` with `n + 2` practical. -/
