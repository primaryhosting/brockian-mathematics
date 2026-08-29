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

theorem mem_hyperperfect_iff {n : ℕ} (hn : 1 < n) :
    n ∈ Hyperperfect ↔ 0 < sigma n - n - 1 ∧ (sigma n - n - 1) ∣ (n - 1) := by
  constructor
  · rintro ⟨k, hk, -, heq⟩
    have hk' := (isHyperperfect_iff hk hn).1 ⟨hk, hn, heq⟩
    refine ⟨?_, ⟨k, by rw [Nat.mul_comm]; omega⟩⟩
    rcases Nat.eq_zero_or_pos (sigma n - n - 1) with h | h
    · rw [h, Nat.mul_zero] at hk'; omega
    · exact h
  · rintro ⟨hs, c, hc⟩
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at hc; omega
      · exact h
    exact ⟨c, (isHyperperfect_iff hc0 hn).2 (by rw [Nat.mul_comm]; omega)⟩

set_option maxRecDepth 10000 in
/-- The hyperperfect numbers below `800` are `6, 21, 28, 301, 325, 496, 697`; here we check
that each of them is indeed hyperperfect. -/
