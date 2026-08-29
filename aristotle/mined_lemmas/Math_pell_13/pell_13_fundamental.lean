/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module doc-comment, and Lean 4 forbids
`import` commands after it, so this file is deliberately import-free.  Mathlib's general
theorem `Pell.exists_of_not_isSquare` (`Mathlib/NumberTheory/Pell.lean`), which states that
for `0 < d` with `¬ IsSquare d` there are `x y : ℤ` with `x ^ 2 - d * y ^ 2 = 1` and `y ≠ 0`,
covers this statement as the special case `d = 13`.  Here we instead give the explicit
fundamental solution, which needs no imports at all and is checked by the kernel.
-/

namespace Math

/-- **Pell's equation for `d = 13`.**  The equation `x² - 13·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0`.  Witness: the fundamental solution
`(x, y) = (649, 180)`, since `649² = 421201 = 13 · 180² + 1`.

(In Mathlib this also follows from `Pell.exists_of_not_isSquare` applied to `d = 13`.) -/

theorem pell_13_fundamental : (649 : ℤ) ^ 2 - 13 * (180 : ℤ) ^ 2 = 1 := by norm_num

end Math

