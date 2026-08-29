import Mathlib

/-!
# Test Pair Nonneg
Category: Riemann Program
Target: Riemann.WeilPositivity.test_pair_nonneg
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


namespace Riemann.WeilPositivity

/-- The quadratic form of the positive-semidefinite matrix `[[2,1],[1,2]]` is nonnegative:
`2*x^2 + 2*x*y + 2*y^2 = (x+y)^2 + x^2 + y^2 ≥ 0`. -/
theorem test_pair_nonneg (x y : ℝ) : 0 ≤ 2*x^2 + 2*x*y + 2*y^2 := by
  have h : 2*x^2 + 2*x*y + 2*y^2 = (x + y)^2 + x^2 + y^2 := by ring
  rw [h]
  positivity

end Riemann.WeilPositivity

#print axioms Riemann.WeilPositivity.test_pair_nonneg

