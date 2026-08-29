import Mathlib

/-!
# Pell 3 — supplementary results

Beyond the existence of a single nontrivial solution of `x² - 3·y² = 1` (see
`Math.pell_3` in `RequestProject/Main.lean`), we record here that the equation has
arbitrarily large solutions, obtained by iterating the fundamental unit `2 + √3`.
-/

namespace Math

/-- Multiplying a solution of `x² - 3·y² = 1` by the fundamental unit `2 + √3`
gives a new solution with strictly larger `y` (when `x ≥ 1`). -/

theorem pell_3_step {x y : ℤ} (h : x ^ 2 - 3 * y ^ 2 = 1) :
    (2 * x + 3 * y) ^ 2 - 3 * (x + 2 * y) ^ 2 = 1 := by
  nlinarith [h]

/-- There are arbitrarily large solutions of `x² - 3·y² = 1`. -/
