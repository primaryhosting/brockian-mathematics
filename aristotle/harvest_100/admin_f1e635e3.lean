/-
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
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

namespace Fibonacci

/-- Consecutive Fibonacci numbers are coprime. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) := by
  induction n with
  | zero => simp [Nat.Coprime]
  | succ k ih =>
      have h : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      unfold Nat.Coprime at ih ⊢
      rw [h, Nat.gcd_comm, Nat.gcd_add_self_left]
      exact ih

end Fibonacci

