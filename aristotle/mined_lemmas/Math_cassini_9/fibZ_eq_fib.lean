/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, valued in `ℤ`: `fibZ 0 = 0`, `fibZ 1 = 1`,
`fibZ (n + 2) = fibZ n + fibZ (n + 1)`. -/

theorem fibZ_eq_fib (n : Nat) : fibZ n = (Nat.fib n : Int) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fibZ, ih n (by omega), ih (n + 1) (by omega), Nat.fib_add_two]
      push_cast
      ring

/-- Cassini's identity at `n = 9`, in terms of `Nat.fib`. -/
