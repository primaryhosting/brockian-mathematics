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

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, ih n (by omega), ih (n + 1) (by omega), Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 10`, stated for Mathlib's `Nat.fib`, deduced from Mathlib's
general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
