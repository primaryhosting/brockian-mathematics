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

namespace RiemannScaffold

/-- The completed Riemann xi function `ξ(s) = s (s-1) Λ(s)`. -/

theorem riemannXi_one_sub (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s := by
  unfold RiemannScaffold.riemannXi
  rw [completedRiemannZeta_one_sub]
  ring

end RiemannXiFunctionalEquation

