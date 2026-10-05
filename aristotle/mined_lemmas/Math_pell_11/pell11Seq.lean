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

def pell11Seq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
              3 * (pell11Seq n).1 + 10 * (pell11Seq n).2)

/-- Every term of `pell11Seq` solves the Pell equation `x² - 11 y² = 1`. -/
