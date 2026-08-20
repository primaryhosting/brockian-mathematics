/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires `import` commands to precede every other command in a file,
including module doc comments, so this file (whose first token must be the header
above) is kept self-contained and uses only Lean core. The Fibonacci numbers are
therefore defined here; `Math.fib` agrees with Mathlib's `Nat.fib`
(`fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/

theorem fib_values : fib 7 = 13 ∧ fib 8 = 21 ∧ fib 9 = 34 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8)^2 = (-1)^8`. -/
