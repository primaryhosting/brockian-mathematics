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

lemma exists_matched_exponents {b : ℕ} (hb : 1 ≤ b) :
    ∃ a, 1 ≤ a ∧ 7 ^ b ≤ 2 * 3 ^ a ∧ 3 ^ a ≤ 8 * 7 ^ b := by
  have hex : ∃ a, 7 ^ b ≤ 2 * 3 ^ a := by
    refine ⟨3 * b, ?_⟩
    calc 7 ^ b ≤ 27 ^ b := Nat.pow_le_pow_left (by norm_num) b
      _ = 3 ^ (3 * b) := by rw [pow_mul]; norm_num
      _ ≤ 2 * 3 ^ (3 * b) := by omega
  classical
  set a := Nat.find hex with ha
  have hspec : 7 ^ b ≤ 2 * 3 ^ a := Nat.find_spec hex
  have hapos : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h; swap
    · exact h
    · exfalso
      rw [h0] at hspec
      have : (7 : ℕ) ≤ 7 ^ b := by
        calc (7 : ℕ) = 7 ^ 1 := (pow_one 7).symm
          _ ≤ 7 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      simp at hspec
      omega
  refine ⟨a, hapos, hspec, ?_⟩
  have hmin : ¬ (7 ^ b ≤ 2 * 3 ^ (a - 1)) := Nat.find_min hex (by omega)
  push_neg at hmin
  have h3 : (3 : ℕ) ^ a = 3 * 3 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    ring
  omega

/-! ## The construction -/

