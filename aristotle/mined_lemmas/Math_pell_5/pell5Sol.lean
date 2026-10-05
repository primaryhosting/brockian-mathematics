/-
# Pell 5 — Mathlib development
Category: Pure Mathematics
Companion to `Math.pell_5` (see `RequestProject/Main.lean`).
Provenance: Aristotle theorem prover (Harmonic)

This file develops the `d = 5` Pell equation over `ℤ` with Mathlib available:
the existence of a nontrivial solution, and the fact that there are
infinitely many solutions, obtained from the powers of the fundamental
unit `9 + 4√5`.
-/
import Mathlib

namespace Math

/-- The `n`-th solution of `x² - 5y² = 1`, obtained as the coefficients of
`(9 + 4√5)ⁿ`: `pell5Sol 0 = (1, 0)` and
`pell5Sol (n+1) = (9xₙ + 20yₙ, 4xₙ + 9yₙ)`. -/

def pell5Sol : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (9 * (pell5Sol n).1 + 20 * (pell5Sol n).2,
              4 * (pell5Sol n).1 + 9 * (pell5Sol n).2)

/-- Every `pell5Sol n` is a solution of `x² - 5y² = 1`. -/
