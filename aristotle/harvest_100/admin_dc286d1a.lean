/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 13`.**
`x² - 13·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`.
The fundamental solution is `(x, y) = (649, 180)`:
`649² = 421201 = 1 + 13 · 180² = 1 + 13 · 32400`.

(Mathlib's general existence theorem for Pell's equation with a non-square
parameter is `Pell.exists_of_not_isSquare`; here the explicit witness gives a
self-contained, computation-checked proof.) -/
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

