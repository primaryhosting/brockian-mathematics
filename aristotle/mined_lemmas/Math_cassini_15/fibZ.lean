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

def fibZ : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibZ n + fibZ (n + 1)

/-- Cassini's identity at `n = 15`: `F(14) * F(16) - F(15)^2 = (-1)^15`. -/
