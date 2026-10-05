/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.**
`x² - 5·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently, one with `x ≠ ±1`).  Explicitly `9² - 5·4² = 81 - 80 = 1`.

Note: the required header of this file is a module docstring, which Lean only accepts
at the very beginning of a file, before any `import`; the proof is therefore written
in plain Lean 4 without importing Mathlib.  With Mathlib available one could instead
obtain a solution from `Pell.pell_eq` / `Pell.xn_sq_sub_dyn_sq` (Mathlib's development
of Pell's equation for `d = a² - 1`), or simply from `decide`/`norm_num` as here. -/
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

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

