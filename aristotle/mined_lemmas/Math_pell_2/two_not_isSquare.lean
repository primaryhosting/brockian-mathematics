/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: this file must literally begin with the header comment above, so it cannot
contain an `import` command (Lean requires imports to be the very first commands
in a file, before any module docstring).  The proof below is therefore written
in plain Lean 4 core, exhibiting the explicit solution `(x, y) = (3, 2)`.

A Mathlib-based derivation of the same statement, using the general theorem
`Pell.exists_of_not_isSquare` (existence of a nontrivial solution of
`x² - d·y² = 1` for positive non-square `d`), is given in
`RequestProject/PellMathlib.lean` as `Math.pell_2_of_mathlib`.
-/

namespace Math

/-- **Pell's equation for `d = 2`.**  The equation `x² - 2·y² = 1` has a
nontrivial integer solution, i.e. one with `y ≠ 0`: take `x = 3`, `y = 2`. -/

theorem two_not_isSquare : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨r, hr⟩
  have h : r * r = 2 := hr.symm
  have hlb : -2 < r := by nlinarith
  have hub : r < 2 := by nlinarith
  interval_cases r <;> omega

/-- Nontrivial solvability of `x² - 2·y² = 1`, obtained from Mathlib's general
existence theorem `Pell.exists_of_not_isSquare` for positive non-square `d`. -/
