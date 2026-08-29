import Mathlib

/-!
# Primorial Phi Shadow
Category: Riemann Program
Target: Riemann.Nicolas.primorial_phi_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann
namespace Nicolas

/-- **Primorial phi shadow.** The monotone shadow of Nicolas' criterion: the real
logarithm is monotone on the positive reals, i.e. for all reals `a b` with
`0 < a` and `a ≤ b` we have `Real.log a ≤ Real.log b`. -/
theorem primorial_phi_shadow :
    ∀ a b : ℝ, 0 < a → a ≤ b → Real.log a ≤ Real.log b := by
  intro a b ha hab
  exact Real.log_le_log ha hab

end Nicolas
end Riemann

