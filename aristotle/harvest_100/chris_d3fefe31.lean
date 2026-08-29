/-!
# Pell 7
Category: Pure Mathematics
Target: Math.pell_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 7`.**
`x² - 7·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently, one different from `(±1, 0)`).  The witness is
`(x, y) = (8, 3)`, since `8² - 7·3² = 64 - 63 = 1`; the solution is
nontrivial in the strong sense that `1 < x` and `0 < y`.

Mathlib's general theory (`Pell.exists_of_not_isSquare` / the
`Pell.Solution₁` API) yields such a solution for every non-square `d > 0`,
but for `d = 7` the explicit witness settles it outright. -/
theorem pell_7 : ∃ x y : Int, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 ∧ 1 < x ∧ 0 < y :=
  ⟨8, 3, by decide, by decide, by decide, by decide⟩

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

