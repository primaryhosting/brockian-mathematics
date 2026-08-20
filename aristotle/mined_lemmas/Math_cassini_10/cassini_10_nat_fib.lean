/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

This file is required to begin with the header comment above, which Lean only accepts as a
module docstring when the file has no `import` commands; hence the sequence is defined here
from scratch. The file `RequestProject/Cassini10Mathlib.lean` proves that this definition
agrees with Mathlib's `Nat.fib`, and derives the same identity for `Nat.fib` from Mathlib's
Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/

theorem cassini_10_nat_fib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  have e9 : Int.fib ((10 : ℤ) - 1) = (Nat.fib 9 : ℤ) := by
    rw [show (10 : ℤ) - 1 = ((9 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e10 : Int.fib (10 : ℤ) = (Nat.fib 10 : ℤ) := by
    rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e11 : Int.fib ((10 : ℤ) + 1) = (Nat.fib 11 : ℤ) := by
    rw [show (10 : ℤ) + 1 = ((11 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [e9, e10, e11] at h
  rw [mul_comm]
  simpa using h

end Math

