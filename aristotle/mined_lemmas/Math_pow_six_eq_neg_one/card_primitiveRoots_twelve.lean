import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/

lemma card_primitiveRoots_twelve : (primitiveRoots 12 ℂ).card = 4 := by
  rw [(Complex.isPrimitiveRoot_exp 12 (by norm_num)).card_primitiveRoots]
  decide

end Math
#print axioms Math.mobius_root_sum_12

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

