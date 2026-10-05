/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 11·y² = 1` has a nontrivial integer solution,
namely `(x, y) = (10, 3)`: `10² - 11 * 3² = 100 - 99 = 1`. -/
theorem pell_11 : ∃ x y : Int, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by decide, by decide⟩

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

/-!
Mathlib-based rederivation of the Pell 11 statement proved in `RequestProject.Math`
(the target theorem `Math.pell_11` is proved there by exhibiting the solution `(10, 3)`;
that file cannot `import Mathlib` because the required header comment must be the first
thing in the file, and Lean requires `import` lines to come first).

The general Mathlib result is `Pell.exists_of_not_isSquare`.
-/

namespace Math

/-- `x² - 11·y² = 1` has a nontrivial integer solution, obtained from the general
Mathlib theorem `Pell.exists_of_not_isSquare` (positive non-square `d` case). -/
theorem pell_11_via_mathlib : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

end Math

