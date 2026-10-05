/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 11`.**

`x² - 11 y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently, one different from `(±1, 0)`).  The fundamental solution is
`(x, y) = (10, 3)`, since `10² - 11 · 3² = 100 - 99 = 1`.

Mathlib's general existence theorem for this is `Pell.exists_of_not_isSquare`
(for `0 < d` with `d` not a perfect square); here the explicit witness is
simpler and keeps the proof self-contained. -/

theorem pell_11' : ∃ x y : Int, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 ∧ 1 < x :=
  ⟨10, 3, by decide, by decide, by decide⟩

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

