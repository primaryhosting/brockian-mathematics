import Mathlib
/-!
# Primorial Phi Shadow
Category: Riemann Program
Target: Riemann.Nicolas.primorial_phi_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Nicolas

/-- Monotonicity of the real logarithm on the positive reals: for all reals `a b`
with `0 < a` and `a ≤ b`, we have `Real.log a ≤ Real.log b`. This is the monotone
"shadow" underlying Nicolas' inequality chain comparing `N/φ(N)` with
`e^γ log log N` over primorials. -/
theorem primorial_phi_shadow (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Real.log a ≤ Real.log b :=
  Real.log_le_log ha hab

end Riemann.Nicolas

#print axioms Riemann.Nicolas.primorial_phi_shadow

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

