/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` commands to be the very first commands in a file, so the
-- header comment above forces this file to be self-contained (no imports).  The Fibonacci
-- numbers are therefore defined here directly, with the standard convention
-- `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

namespace Math

/-- The Fibonacci numbers, valued in `ℤ`: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

/-- Cassini's identity at `n = 3`: `F 2 * F 4 - F 3 ^ 2 = (-1) ^ 3`. -/
