/-
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Fibonacci

/-- **d'Ocagne's identity, addition form.**  For all `m n : ℕ`,
`F (m + n + 1) = F (m+1) * F (n+1) + F m * F n`, stated over `ℤ`.
This is `Nat.fib_add` from Mathlib, cast to the integers. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add]
  push_cast
  ring

/-- Auxiliary shifted form of d'Ocagne's identity:
`F (n+k) * F (n+1) - F (n+k+1) * F n = (-1)^n * F k`. -/
theorem dOcagne_shift (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := by
        rw [Nat.fib_add_two]
      have h2 : Nat.fib (n + 1 + k + 1) = Nat.fib (n + k) + Nat.fib (n + k + 1) := by
        have : n + 1 + k + 1 = (n + k) + 2 := by omega
        rw [this, Nat.fib_add_two]
      have h3 : n + 1 + k = n + k + 1 := by omega
      rw [h1, h2, h3]
      push_cast
      push_cast at ih
      linear_combination -ih

/-- **d'Ocagne's identity, subtraction form.**  For `n ≤ m`,
`F m * F (n+1) - F (m+1) * F n = (-1)^n * F (m - n)`. -/
theorem dOcagne_sub (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  simpa using dOcagne_shift n k

end Fibonacci

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

