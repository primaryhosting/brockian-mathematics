/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
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

set_option grind.warning false

namespace Fibonacci

/-- A shifted form of d'Ocagne's identity, stated over `ℤ` and free of natural subtraction:
`F (a + r + 1) * F a - F (a + 1) * F (a + r) = (-1) ^ (a + 1) * F r`. -/

theorem docagne (a r : ℕ) :
    (Nat.fib (a + r + 1) : ℤ) * Nat.fib a - (Nat.fib (a + 1) : ℤ) * Nat.fib (a + r)
      = (-1) ^ (a + 1) * Nat.fib r := by
  induction a with
  | zero => simp
  | succ k ih =>
      have h1 : Nat.fib (k + 1 + r + 1) = Nat.fib (k + r + 1) + Nat.fib (k + r) := by
        have : k + 1 + r + 1 = (k + r) + 2 := by ring
        rw [this, Nat.fib_add_two]
        ring
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have h3 : k + 1 + r = (k + r) + 1 := by ring
      have h4 : k + 1 + 1 = k + 2 := by ring
      rw [h1, h3, h4, h2]
      push_cast
      have hp : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by ring
      rw [hp]
      linear_combination -ih

/-- Catalan's identity in addition form (no natural subtraction):
`F (m + r) ^ 2 - F m * F (m + 2 * r) = (-1) ^ m * F r ^ 2`. -/
