import Mathlib
/-!
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4` in `ZMod 5`:
rays `2` and `3` are square-free. -/
theorem square_mod5_mem : ∀ n : ZMod 5, n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  decide

/-- Integer form: for every `n : ℤ`, the class of `n ^ 2` in `ZMod 5` is `0`, `1`, or `4`. -/
theorem square_mod5_mem_int (n : ℤ) :
    ((n : ℤ) : ZMod 5) ^ 2 = 0 ∨ ((n : ℤ) : ZMod 5) ^ 2 = 1 ∨ ((n : ℤ) : ZMod 5) ^ 2 = 4 :=
  square_mod5_mem (n : ZMod 5)

end Brockian.ConeLine

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

