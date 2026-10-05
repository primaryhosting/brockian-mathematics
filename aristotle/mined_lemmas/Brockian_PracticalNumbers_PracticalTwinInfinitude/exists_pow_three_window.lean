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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/

theorem exists_pow_three_window (x : ℕ) (hx : 0 < x) : ∃ j, x ≤ 3 ^ j ∧ 3 ^ j < 3 * x := by
  classical
  have hex : ∃ j, x ≤ 3 ^ j := ⟨x, le_of_lt (Nat.lt_pow_self (by norm_num))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    have h0 : (3:ℕ) ^ 0 = 1 := pow_zero 3
    omega
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    push_neg at hmin
    have heq : (3:ℕ) ^ (Nat.find hex) = 3 * 3 ^ (Nat.find hex - 1) := by
      conv_lhs => rw [show Nat.find hex = (Nat.find hex - 1) + 1 by omega]
      ring
    omega

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
