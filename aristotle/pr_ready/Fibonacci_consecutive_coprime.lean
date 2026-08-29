/-!
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Statement: Consecutive Fibonacci numbers are coprime: for all n : Nat, Nat.Coprime (Nat.fib n) (Nat.fib (n+1)). (Use Mathlib's Nat.fib_coprime_fib_succ if present, else induction.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Fibonacci

/-- Consecutive Fibonacci numbers are coprime. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) :=
  Nat.fib_coprime_fib_succ n

end Fibonacci

