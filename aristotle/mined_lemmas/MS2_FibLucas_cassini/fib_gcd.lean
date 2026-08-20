import Mathlib
namespace MS2.FibLucas

/-- Cassini's identity. The statement is cast to `ℤ`, since `(-1)^n` does not
make sense in `ℕ`. -/

theorem fib_gcd (m n : ℕ) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  (Nat.fib_gcd m n).symm

