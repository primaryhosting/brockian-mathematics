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

def quadraticInvariant (p q : R) (x : ℕ → R) (n : ℕ) : R :=
  x (n + 1) ^ 2 - p * x n * x (n + 1) - q * x n ^ 2

/-- The quadratic invariant is also scaled by `-q` at each recurrence step. -/
