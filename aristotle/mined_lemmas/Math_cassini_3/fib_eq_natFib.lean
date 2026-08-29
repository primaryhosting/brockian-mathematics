/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 3`, phrased with `Nat.fib`. -/
