/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 6`.**

`x² - 6·y² = 1` has a nontrivial integer solution, i.e. a solution with `y ≠ 0`
(so that `x ≠ ±1` as well).  A witness is `(x, y) = (5, 2)`, since `25 - 24 = 1`.

The file carries no `import` line because the required header comment must be the very
first thing in the file, and Lean requires `import` commands to precede all other syntax;
the proof therefore uses only core `Int` arithmetic and needs no library support. -/
theorem pell_6 : ∃ x y : Int, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by decide, by decide⟩

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

