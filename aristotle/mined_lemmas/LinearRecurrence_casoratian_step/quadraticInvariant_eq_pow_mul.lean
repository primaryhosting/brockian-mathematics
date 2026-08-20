import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Invariants of second-order linear recurrences

This file develops two algebraic invariants shared by every recurrence

`x (n + 2) = p * x (n + 1) + q * x n`.

The results work over an arbitrary commutative ring, so they apply equally to
integer sequences, polynomial sequences, and recurrences modulo an integer.
-/

namespace LinearRecurrence

variable {R : Type*} [CommRing R]

/-- The discrete Wronskian (Casoratian) of two sequences. -/

theorem quadraticInvariant_eq_pow_mul
    (p q : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n) :
    ∀ n, quadraticInvariant p q x n =
      (-q) ^ n * quadraticInvariant p q x 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quadraticInvariant_step p q x hx n, ih, pow_succ', mul_assoc]

/-- When `q = -1`, the quadratic expression is genuinely constant. -/
