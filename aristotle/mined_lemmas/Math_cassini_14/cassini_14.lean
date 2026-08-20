import Mathlib
/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the requested header comment appears immediately after the import.

namespace Math

/-- **Cassini's identity at `n = 14`**: `F(13) · F(15) − F(14)² = (−1)^14`,
where `F` is the Fibonacci sequence (`Nat.fib`), computed in `ℤ`.

Here `F(13) = 233`, `F(14) = 377`, `F(15) = 610`, and `233 · 610 − 377² = 142130 − 142129 = 1`. -/

theorem cassini_14 :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1 : ℤ) ^ 14 := by
  norm_num

/-- The general Cassini identity, from which the `n = 14` case follows:
`F(n+1) · F(n+3) − F(n+2)² = (−1)^n`. -/
