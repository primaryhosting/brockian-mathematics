/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/- Note: the required header above is a module docstring, which Lean does not permit
before `import` commands, so this file is written using only Lean's core library
(implicitly available `Init`); no Mathlib lemmas are needed. -/

namespace Math

/-- **Pell's equation for 13.** `x² - 13·y² = 1` has a nontrivial integer solution:
the fundamental solution `(x, y) = (649, 180)`, since `649² - 13·180² = 421201 - 421200 = 1`.
Nontriviality is recorded as `1 < x` and `0 < y`. -/
theorem pell_13 : ∃ x y : Int, x ^ 2 - 13 * y ^ 2 = 1 ∧ 1 < x ∧ 0 < y :=
  ⟨649, 180, by decide, by decide, by decide⟩

end Math

#print axioms Math.pell_13

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

