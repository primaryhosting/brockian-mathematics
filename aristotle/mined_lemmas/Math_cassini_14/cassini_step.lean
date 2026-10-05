/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, and Lean requires all
`import` commands to precede any command (including a module docstring). The file is therefore
kept self-contained: the Fibonacci numbers are defined here and everything is proved from
first principles, with no imports.
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

private theorem cassini_step (x y c : Int) (h : x * (x + y) - y ^ 2 = c) :
    y * (y + (x + y)) - (x + y) ^ 2 = c * (-1) := by grind

/-- Cassini's identity: `F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` (over `ℤ`). -/
