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

theorem quadraticInvariant_constant
    (p : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) - x n) :
    ∀ n, quadraticInvariant p (-1) x n = quadraticInvariant p (-1) x 0 := by
  intro n
  have hrec : ∀ k, x (k + 2) = p * x (k + 1) + (-1) * x k := by
    intro k
    simpa [sub_eq_add_neg] using hx k
  rw [quadraticInvariant_eq_pow_mul p (-1) x hrec n]
  simp

end LinearRecurrence

