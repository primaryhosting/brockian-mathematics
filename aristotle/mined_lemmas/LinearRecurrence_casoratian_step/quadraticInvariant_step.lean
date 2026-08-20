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

theorem quadraticInvariant_step
    (p q : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n)
    (n : ℕ) :
    quadraticInvariant p q x (n + 1) =
      -q * quadraticInvariant p q x n := by
  simp only [quadraticInvariant]
  rw [hx n]
  ring

/-- Closed form of the quadratic invariant. This subsumes Cassini-type identities. -/
