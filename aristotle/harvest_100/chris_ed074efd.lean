/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.**

The equation `x² - 5·y² = 1` has a nontrivial integer solution, i.e. a solution
other than the trivial ones `(±1, 0)`: indeed `9² - 5·4² = 81 - 80 = 1`.

(The statement is phrased over `Int`; the file needs no imports, so the proof is
checked by the kernel with no axioms at all.)
-/
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨9, 4, by decide, by decide, by decide, by decide⟩

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

