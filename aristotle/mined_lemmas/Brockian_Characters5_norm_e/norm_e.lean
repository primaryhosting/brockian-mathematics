/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  rw [e, norm_pow, norm_omega, one_pow]

end Characters5
end Brockian

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

