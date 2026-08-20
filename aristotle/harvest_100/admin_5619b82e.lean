import Mathlib

/-!
# Pell 6 — alternative proof via Mathlib's general Pell theory

Companion to `RequestProject/Pell6.lean`.  The main target `Math.pell_6` is proved there
by exhibiting the explicit solution `(5, 2)`.  Here we instead derive the same statement
from the existing Mathlib result `Pell.exists_of_not_isSquare`, which states that for any
positive non-square integer `d` the equation `x ^ 2 - d * y ^ 2 = 1` has a solution with
`y ≠ 0`.
-/

namespace Math

/-- `x² - 6·y² = 1` has a nontrivial integer solution, obtained from
`Pell.exists_of_not_isSquare` applied to `d = 6` (positive and not a square). -/
theorem pell_6_via_mathlib : ∃ x y : ℤ, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (d := 6) (by norm_num) (by decide +kernel)

end Math

/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0`: take `(x, y) = (5, 2)`, since `5² - 6·2² = 25 - 24 = 1`. -/
theorem pell_6 : ∃ x y : Int, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by decide, by decide⟩

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

