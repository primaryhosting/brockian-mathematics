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

theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
  have h1 : m + r - r = m := by omega
  have h2 : m + r + r = m + 2 * r := by ring
  rw [h1, h2]
  exact catalan_add m r

end Fibonacci

