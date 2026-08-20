/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires all `import` commands to precede any other command, including
module doc comments.  Since the requested header must be the very first thing in
this file, the file is kept self-contained (no imports beyond the core prelude)
and the Fibonacci sequence is defined directly below with the standard recursion,
matching `Nat.fib` (`F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
