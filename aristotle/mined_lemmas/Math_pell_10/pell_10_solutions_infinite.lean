import Mathlib

/-!
# Pell 10 (Mathlib companion)

The main target `Math.pell_10` lives in `RequestProject/Pell10.lean`.  Here we record the
same statement phrased with Mathlib's `ℤ`, together with the stronger fact that the Pell
equation `x² - 10·y² = 1` has infinitely many integer solutions, obtained by iterating the
fundamental solution `(19, 6)`.
-/

namespace Math

/-- Iterating the fundamental solution `(19, 6)` of `x² - 10·y² = 1`:
`(x, y) ↦ (19x + 60y, 6x + 19y)` (multiplication by `19 + 6√10`). -/

theorem pell_10_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 10 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hb⟩
  obtain ⟨x, y, hxy, hy⟩ := pell_10_infinitely_many b
  have := hb (show (x, y) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 10 * p.2 ^ 2 = 1} from hxy)
  exact absurd this.2 (not_le.mpr hy)

end Math

/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 10`.**

The equation `x² - 10·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently `x ≠ ±1`): indeed `19² - 10·6² = 361 - 360 = 1`.

Note on the file layout: the required header above is a module docstring, which must be the
first command in a Lean file; no `import` may follow it, so this file is written using Lean
core only (`Int` is the same type as Mathlib's `ℤ`).  A Mathlib-based companion file,
`RequestProject/Pell10Mathlib.lean`, additionally shows that the equation has infinitely
many solutions. -/
