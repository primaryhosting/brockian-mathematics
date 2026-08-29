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
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * Nat.fib (m + 2 * r)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases m with
  | zero => simp
  | succ k =>
      rw [show k + 1 + r = k + r + 1 from by ring, show k + 1 + 2 * r = (k + r) + r + 1 from by ring]
      have e1 : (Nat.fib (k + r + 1) : ℤ)
          = (Nat.fib k : ℤ) * Nat.fib r + (Nat.fib (k + 1) : ℤ) * Nat.fib (r + 1) := by
        rw [Nat.fib_add]; push_cast; ring
      have e2 : (Nat.fib ((k + r) + r + 1) : ℤ)
          = (Nat.fib (k + r) : ℤ) * Nat.fib r + (Nat.fib (k + r + 1) : ℤ) * Nat.fib (r + 1) := by
        rw [Nat.fib_add]; push_cast; ring
      have key := docagne k r
      linear_combination (Nat.fib r : ℤ) * key + (Nat.fib (k + r + 1) : ℤ) * e1
        - (Nat.fib (k + 1) : ℤ) * e2

/-- **Catalan's identity** (a generalisation of Cassini's identity): for `r ≤ n`,
`F n ^ 2 - F (n - r) * F (n + r) = (-1) ^ (n - r) * F r ^ 2`. -/
theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
  have h1 : m + r - r = m := by omega
  have h2 : m + r + r = m + 2 * r := by ring
  rw [h1, h2]
  exact catalan_add m r

end Fibonacci

