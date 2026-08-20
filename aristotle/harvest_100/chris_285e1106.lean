import Mathlib
/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(i.e. one with `y ≠ 0`): take `x = 3`, `y = 1`, since `3² - 8·1² = 9 - 8 = 1`. -/
theorem pell_8 : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by norm_num, one_ne_zero⟩

/-- The same statement, obtained instead from the general existence theorem for Pell's
equation in Mathlib, `Pell.exists_of_not_isSquare`, applied to the non-square `d = 8`. -/
theorem pell_8' : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

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

