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

theorem pell11Seq_bounds (n : ℕ) : 1 ≤ (pell11Seq n).1 ∧ (n : ℤ) ≤ (pell11Seq n).2 := by
  induction n with
  | zero => norm_num [pell11Seq]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hb : (0 : ℤ) ≤ (pell11Seq n).2 := le_trans (by positivity) h2
      have h : pell11Seq (n + 1) =
          (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
           3 * (pell11Seq n).1 + 10 * (pell11Seq n).2) := rfl
      rw [h]
      constructor
      · simpa using by linarith
      · push_cast
        simpa using by linarith

/-- Strengthening of `Math.pell_11`: the Pell equation `x² - 11 y² = 1` has solutions with
arbitrarily large `y`, hence infinitely many integer solutions. -/
