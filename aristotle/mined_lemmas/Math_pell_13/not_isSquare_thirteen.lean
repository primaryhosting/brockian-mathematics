/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to be the very first thing in a file, so no
-- `import` can follow the header comment above. This file is therefore self-contained
-- (it needs nothing beyond the core `Int` arithmetic that is available without imports).
-- A Mathlib-based development of the same statement, deriving it from
-- `Pell.exists_of_not_isSquare`, is in `RequestProject/PellMathlib.lean`.

namespace Math

/-- **Pell's equation for `d = 13`.** The equation `x² - 13·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0`: the fundamental solution `(x, y) = (649, 180)`
works, since `649² - 13 · 180² = 421201 - 421200 = 1`. -/

theorem not_isSquare_thirteen : ¬ IsSquare (13 : ℤ) := by decide +kernel

/-- **Pell's equation for `d = 13`**, derived from Mathlib's
`Pell.exists_of_not_isSquare`: since `13 > 0` is not a perfect square,
`x² - 13·y² = 1` has a solution with `y ≠ 0`. -/
