import Mathlib

/-!
# Pell 11 (companion file)

This file complements `RequestProject/Main.lean`, which contains the target theorem
`Math.pell_11` stated over core `Int` (the target file must begin with a fixed header
comment, and in Lean 4 a module docstring cannot precede an `import`, so that file is
Mathlib-free).

Here we restate the result over `ℤ` with Mathlib available, and strengthen it:
the Pell equation `x² - 11 y² = 1` has infinitely many solutions, obtained by iterating
the fundamental solution `(10, 3)`.
-/

namespace Math

/-- Iterating the fundamental solution `(10, 3)` of `x² - 11 y² = 1`:
`(a, b) ↦ (10a + 33b, 3a + 10b)`, starting from the trivial solution `(1, 0)`. -/

theorem pell_11_int : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by norm_num, by norm_num⟩

/-- The set of integer solutions of `x² - 11 y² = 1` is infinite. -/
