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

/-- The sum of all divisors of `n`, i.e. `σ₁ n`. -/

theorem isHyperperfect_iff {n : ℕ} (hn : 1 < n) :
    IsHyperperfect n ↔ 0 < restrictedSum n ∧ restrictedSum n ∣ (n - 1) := by
  constructor
  · rintro ⟨k, hk, -, hkn⟩
    have hr : 0 < restrictedSum n := by
      rcases Nat.eq_zero_or_pos (restrictedSum n) with h | h
      · rw [h] at hkn; omega
      · exact h
    exact ⟨hr, ⟨k, by rw [Nat.mul_comm]; omega⟩⟩
  · rintro ⟨hr, m, hm⟩
    refine ⟨m, ?_, hn, ?_⟩
    · rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    · rw [Nat.mul_comm]; omega

