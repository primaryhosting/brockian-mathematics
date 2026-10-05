/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci numbers, valued in `ℤ`: `fibZ 0 = 0`, `fibZ 1 = 1`,
`fibZ (n+2) = fibZ n + fibZ (n+1)`. -/

theorem fibZ_eq_fib (n : Nat) : fibZ n = (Nat.fib n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      rw [fibZ, ih m (by omega), ih (m + 1) (by omega), Nat.fib_add_two]
      push_cast
      ring

/-- Cassini's identity at `n = 15`, stated with Mathlib's `Nat.fib`. -/
