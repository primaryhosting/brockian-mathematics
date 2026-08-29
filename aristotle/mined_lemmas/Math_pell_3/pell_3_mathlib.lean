/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires `import` commands to be the very first
commands in a file, and a module docstring `/-! ... -/` counts as a command.
Since the header above must literally begin the file, this module carries no
imports and is developed from the Lean core library only; the statements below
are therefore fully self-contained.  A Mathlib-based companion development
(using `ℤ`, `Set.Infinite`, ...) lives in `RequestProject/PellMathlib.lean`.
-/

namespace Math

/-- The Pell equation `x² - 3·y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0` (equivalently `x ≠ ±1`).  Indeed `2² - 3·1² = 1`. -/

theorem pell_3_mathlib : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- The set of integer solutions of `x² - 3·y² = 1` is infinite. -/
