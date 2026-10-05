/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0`: take `(x, y) = (9, 4)`, since `81 - 5 * 16 = 1`.

(The header comment required for this file must be the first thing in the file, and Lean
forbids `import` after it, so this module is stated and proved using only Lean's core
`Int` arithmetic rather than Mathlib. In Mathlib the general existence statement for a
non-square `d` is `Pell.exists_of_not_isSquare`.) -/

theorem pell_5_of_mathlib : ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_five

end Math

