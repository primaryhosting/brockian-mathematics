/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(Defined here rather than imported, since the required file header must be the
very first thing in the file, which rules out an `import` line.) -/

theorem F_eq_fib (n : Nat) : F n = Nat.fib n := by
  induction n using F.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
      rw [F, ih1, ih2, Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 10`, stated with Mathlib's `Nat.fib`. -/
