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
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

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

/-
Companion module: the same statement as `Math.pell_5`, obtained from Mathlib's general
existence theorem for Pell's equation, `Pell.exists_of_not_isSquare`.

This lives in a separate module because `RequestProject/Math.lean` is required to begin
with a fixed header comment, after which Lean does not permit `import` commands.
-/
import Mathlib

namespace Math

/-- `5` is not a square in `ℤ`. -/
theorem not_isSquare_five : ¬ IsSquare (5 : ℤ) := by decide +kernel

/-- Pell's equation `x² - 5·y² = 1` has a nontrivial integer solution, derived from
Mathlib's `Pell.exists_of_not_isSquare`. -/
theorem pell_5_of_mathlib : ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_five

end Math

