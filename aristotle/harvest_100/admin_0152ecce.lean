/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 8`.**

`x² − 8·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently `x ≠ ±1`): take `(x, y) = (3, 1)`, since `3² − 8·1² = 9 − 8 = 1`.

Note: the file must open with the required header comment, which Lean does not
allow to precede an `import`; the proof is therefore written in core Lean 4
(no Mathlib lemmas are needed) and is checked by the kernel via `decide`. -/
theorem pell_8 : ∃ x y : Int, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by decide, by decide⟩

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

