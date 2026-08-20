/-!
# Primorial Phi Shadow
Category: Riemann Program
Target: Riemann.Nicolas.primorial_phi_shadow
Statement: Nicolas' criterion compares N_k/phi(N_k) with e^gamma log log N_k over primorials N_k. Prove the monotone shadow: for all real a b, 0 < a -> a <= b -> Real.log a <= Real.log b (log-monotonicity, the engine of Nicolas' inequality chain).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann.Nicolas

/-- Monotonicity of `Real.log` on the positive reals: the engine of the
inequality chain in Nicolas' criterion. -/
theorem primorial_phi_shadow (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Real.log a ≤ Real.log b :=
  Real.log_le_log ha hab

end Riemann.Nicolas
#print axioms Riemann.Nicolas.primorial_phi_shadow

