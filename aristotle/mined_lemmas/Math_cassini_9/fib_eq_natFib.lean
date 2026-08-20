/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n + 2) = F n + F (n + 1)`.
    This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_natFib`). -/

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`, obtained from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
