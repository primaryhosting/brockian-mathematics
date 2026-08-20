/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pell's equation `x² - 5·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0`: the fundamental solution is `(x, y) = (9, 4)`,
since `9² - 5·4² = 81 - 80 = 1`. -/

theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

#print axioms Math.pell_5

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

