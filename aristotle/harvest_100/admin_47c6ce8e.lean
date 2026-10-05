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
theorem pell_13 : ∃ x y : Int, x ^ 2 - 13 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨649, 180, by decide, by decide⟩

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
# Pell 13 — the Mathlib route

Companion to `RequestProject/Math.lean`.  The target theorem `Math.pell_13` is proved there
with an explicit witness (that file must start with a fixed module doc-comment, which forbids
`import` commands, so it is import-free).

Here we record the same statement obtained from Mathlib's general existence theorem
`Pell.exists_of_not_isSquare`, and check that the two agree.
-/

namespace Math

/-- `13` is not a square in `ℤ`. -/
theorem not_isSquare_thirteen : ¬ IsSquare (13 : ℤ) := by decide +kernel

/-- **Pell's equation for `d = 13`**, via Mathlib's `Pell.exists_of_not_isSquare`:
since `0 < 13` and `13` is not a perfect square, `x² - 13·y² = 1` has a solution with `y ≠ 0`. -/
theorem pell_13_via_mathlib : ∃ x y : ℤ, x ^ 2 - 13 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_thirteen

/-- The explicit fundamental solution `(649, 180)` indeed solves `x² - 13·y² = 1`. -/
theorem pell_13_fundamental : (649 : ℤ) ^ 2 - 13 * (180 : ℤ) ^ 2 = 1 := by norm_num

end Math

