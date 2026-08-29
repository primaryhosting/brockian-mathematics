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

/-- **Fundamental theorem of algebra.** Every nonconstant complex polynomial (i.e. one of
positive degree) has a complex root. -/

theorem fta_algebra_contrapositive (p : Polynomial ℂ) (h : ∀ z : ℂ, p.eval z ≠ 0) :
    p.degree ≤ 0 := by
  by_contra hd
  obtain ⟨z, hz⟩ := fta_algebra p (lt_of_not_ge hd)
  exact h z hz

end Math

#print axioms Math.fta_algebra
#print axioms Math.fta_algebra_contrapositive

