/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Statement: x² − 10·y² = 1 has a nontrivial integer solution (Pell).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The Pell equation `x² - 10·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`), e.g. `(x, y) = (19, 6)`. -/
theorem pell_10 : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine ⟨19, 6, by norm_num, by norm_num⟩

end Math


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

