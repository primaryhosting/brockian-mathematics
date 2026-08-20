import Mathlib

/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- A perfect square is congruent to `0` or `1` modulo `4`. -/

theorem sq_mod_four_eq_zero_or_one (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    subst hk
    have h : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [h, Nat.mul_mod_right]
  · right
    subst hk
    have h : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    rw [h, Nat.mul_add_mod]

/-- A sum of two squares is never congruent to `3` modulo `4`. -/
