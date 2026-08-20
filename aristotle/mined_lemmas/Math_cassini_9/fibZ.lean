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

def fibZ : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibZ n + fibZ (n + 1)

/-- Cassini's identity at `n = 9`: `F(8) * F(10) - F(9)^2 = (-1)^9`. -/
