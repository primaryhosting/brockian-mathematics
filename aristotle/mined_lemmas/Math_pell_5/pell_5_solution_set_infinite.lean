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

theorem pell_5_solution_set_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨x, y, hxy, hyN⟩ := pell_5_infinitely_many N.2
  exact absurd (hN (show (x, y) ∈ _ from hxy)).2 (not_le.mpr hyN)

end Math

/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.**
The equation `x² - 5·y² = 1` has a nontrivial integer solution, i.e. a solution
with `y ≠ 0` (equivalently, one other than `(±1, 0)`).  Witness: `x = 9`, `y = 4`,
since `81 - 5 * 16 = 1`. -/
