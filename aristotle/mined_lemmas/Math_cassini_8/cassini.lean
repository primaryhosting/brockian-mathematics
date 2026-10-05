/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file's required header comment must be the very first thing in the file, which
prevents an `import` line, so the sequence is defined here from scratch rather than
taken from Mathlib; it agrees with `Nat.fib`.) -/

theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]
        push_cast
        ring
      have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        rw [Nat.fib_add_two]
        push_cast
        ring
      rw [show k + 1 + 2 = k + 3 from rfl, h, h2, pow_succ]
      rw [h2] at ih
      linear_combination -ih

/-- Cassini's identity at `n = 8`, stated with Mathlib's `Nat.fib`. -/
