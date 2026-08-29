/-!
# Pell 7
Category: Pure Mathematics
Target: Math.pell_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 7`.**  The equation `x² - 7·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so it is not one of the trivial solutions
`(±1, 0)`).  Witness: `8² - 7·3² = 64 - 63 = 1`. -/
theorem pell_7 : ∃ x y : Int, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨8, 3, by decide, by decide⟩

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

