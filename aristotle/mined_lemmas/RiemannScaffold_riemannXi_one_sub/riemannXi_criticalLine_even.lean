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

theorem riemannXi_criticalLine_even (t : ℂ) :
    RiemannScaffold.riemannXi (1 / 2 + t * Complex.I)
      = RiemannScaffold.riemannXi (1 / 2 - t * Complex.I) := by
  have h := riemannXi_reflect (1 / 2 + t * Complex.I)
  have he : (1 : ℂ) - (1 / 2 + t * Complex.I) = 1 / 2 - t * Complex.I := by ring
  rw [he] at h
  exact h.symm

