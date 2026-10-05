/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 3`.**  The equation `x² - 3·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).

Mathlib contains the general existence theorem for Pell's equation,
`Pell.exists_of_not_isSquare : 0 < d → ¬IsSquare d → ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`,
which applies to `d = 3` since `3` is not a perfect square; here we instead exhibit the
explicit fundamental solution `(x, y) = (2, 1)`, which keeps the proof self-contained
and decidable. -/
theorem pell_3 : ∃ x y : Int, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨2, 1, by decide, by decide, by decide, by decide⟩

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

