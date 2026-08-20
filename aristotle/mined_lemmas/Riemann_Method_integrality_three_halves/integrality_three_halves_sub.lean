import Mathlib
import RequestProject.IntegralityThreeHalves

/-!
# Integrality Three Halves — Mathlib restatements

The target theorem `Riemann.Method.integrality_three_halves` lives in
`RequestProject/IntegralityThreeHalves.lean`, which must begin with a fixed header
comment and therefore cannot carry an `import` line; it is proved in Lean core.

This companion file imports Mathlib and records the equivalent formulations
`m ^ 2 ≥ 3 * m - 2` over `ℕ` and `(m - 1) * (m - 2) ≥ 0` over `ℤ`.
-/

namespace Riemann.Method

/-- Restatement over `ℕ` with `ℕ`-subtraction: `m ^ 2 ≥ 3 * m - 2`. -/

theorem integrality_three_halves_sub (m : ℕ) : 3 * m - 2 ≤ m ^ 2 :=
  Nat.sub_le_of_le_add (integrality_three_halves m)

/-- Restatement over `ℤ`: `(m - 1) * (m - 2) ≥ 0` for a natural number `m`. -/
