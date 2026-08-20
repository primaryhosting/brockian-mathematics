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

/-!
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- For every natural number `m`, `3 * m ≤ m ^ 2 + 2`, equivalently `(m-1)*(m-2) ≥ 0`. -/
theorem integrality_three_halves (m : ℕ) : 3 * m ≤ m ^ 2 + 2 := by
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · have h : (m + 1 + 1) ^ 2 = m * m + 4 * m + 4 := by ring
    omega

end Riemann.Method

#print axioms Riemann.Method.integrality_three_halves

