/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 2`.**
The equation `x² - 2·y² = 1` has a nontrivial integer solution, i.e. one with
`y ≠ 0` (equivalently, one other than `(±1, 0)`): take `(x, y) = (3, 2)`, since
`3² - 2·2² = 9 - 8 = 1`.

(The statement is phrased with `x * x` and `y * y` rather than `x ^ 2`, `y ^ 2`,
because the file uses no imports beyond Lean's core prelude.) -/
theorem pell_2 : ∃ x y : Int, x * x - 2 * (y * y) = 1 ∧ y ≠ 0 :=
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

