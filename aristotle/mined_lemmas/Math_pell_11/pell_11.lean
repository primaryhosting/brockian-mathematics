/-
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header above uses `/- -/` rather than `/-! -/` because a module
-- docstring is a command and may not precede `import` lines in Lean 4.

import Mathlib

namespace Math

/-- **Pell's equation for `d = 11`.** The equation `x² - 11·y² = 1` has a
nontrivial integer solution, i.e. one with `y ≠ 0`: take `(x, y) = (10, 3)`,
since `100 - 11 * 9 = 1`.

Mathlib also provides the general existence result
`Pell.exists_of_not_isSquare : 1 < d → ¬IsSquare d → ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`;
see `pell_11_via_mathlib` below for a derivation using it. -/

theorem pell_11 : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by norm_num, by norm_num⟩

/-- The same statement obtained from Mathlib's general theorem
`Pell.exists_of_not_isSquare`, using that `11` is not a perfect square. -/
