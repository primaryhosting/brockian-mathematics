import Mathlib

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
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

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root. -/

theorem fta_algebra_of_nonconstant (p : Polynomial ℂ) (hp : ∀ c : ℂ, p ≠ Polynomial.C c) :
    ∃ z : ℂ, p.IsRoot z := by
  refine fta_algebra p ?_
  by_contra h
  exact hp (p.coeff 0) (Polynomial.eq_C_of_degree_le_zero (not_lt.mp h))

end Math

#print axioms Math.fta_algebra

