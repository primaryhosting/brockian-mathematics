import Mathlib
namespace MS2.FibLucas

/-- Cassini's identity. The statement is cast to `ℤ`, since `(-1)^n` does not
make sense in `ℕ`. -/

theorem fib_add (m n : ℕ) :
    Nat.fib (m+n+1) = Nat.fib (m+1)*Nat.fib (n+1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add, add_comm]

