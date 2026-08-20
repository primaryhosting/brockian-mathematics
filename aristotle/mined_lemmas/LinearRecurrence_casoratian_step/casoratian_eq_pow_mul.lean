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

theorem casoratian_eq_pow_mul
    (p q : R) (x y : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n)
    (hy : ∀ n, y (n + 2) = p * y (n + 1) + q * y n) :
    ∀ n, casoratian x y n = (-q) ^ n * casoratian x y 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [casoratian_step p q x y hx hy n, ih, pow_succ', mul_assoc]

/-- A quadratic expression naturally attached to a second-order recurrence. -/
