import Mathlib
namespace Brockian.Cassini
/-- Cassini's identity for Fibonacci numbers: F_n·F_{n+2} − F_{n+1}² = (−1)^{n+1}. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2)) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  sorry
end Brockian.Cassini
