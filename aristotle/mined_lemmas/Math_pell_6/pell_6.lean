/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution, i.e. one
with `y ≠ 0`: take `(x, y) = (5, 2)`, since `5² - 6·2² = 25 - 24 = 1`.

Since the required header comment must be the first thing in this file, the file cannot
carry an `import` line (Lean requires imports to precede any module documentation), so the
statement is phrased with core `Int` multiplication `x * x` in place of `x ^ 2`.  A version
using `^` and stated over `ℤ`, together with the fact that there are infinitely many
solutions, is proved in `RequestProject.Pell6Extra`. -/

theorem pell_6 : ∃ x y : Int, x * x - 6 * (y * y) = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by decide, by decide⟩

end Math

import Mathlib

/-!
# Pell 6 (Mathlib version)

Companion to `RequestProject.Pell6`: the Pell equation `x² - 6·y² = 1` stated over `ℤ`
with `^`, plus the fact that it has infinitely many solutions.
-/

namespace Math

/-- `x² - 6·y² = 1` has a nontrivial integer solution, namely `(5, 2)`. -/
