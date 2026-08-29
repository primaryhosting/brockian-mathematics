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
theorem pell_2 : ∃ x y : Int, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 2, by decide, by decide⟩

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Pell's equation for `d = 2`, via Mathlib's general theory

This companion file re-derives the statement of `Math.pell_2` from Mathlib's
`Pell.exists_of_not_isSquare`.
-/

namespace Math

/-- `2` is not a square in `ℤ`. -/
theorem two_not_isSquare : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨r, hr⟩
  have h : r * r = 2 := hr.symm
  have hlb : -2 < r := by nlinarith
  have hub : r < 2 := by nlinarith
  interval_cases r <;> omega

/-- Nontrivial solvability of `x² - 2·y² = 1`, obtained from Mathlib's general
existence theorem `Pell.exists_of_not_isSquare` for positive non-square `d`. -/
theorem pell_2_of_mathlib : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) two_not_isSquare

end Math

