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

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `F(7) = 13`, `F(8) = 21`, `F(9) = 34`. -/
