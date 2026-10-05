import Mathlib

/-!
# Rank Trace C General
Category: Riemann Program
Target: Riemann.method.rank_trace_c_general
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
namespace method

/-- Scalar core of the general-`c` rank-trace inequality: for all real `x` and `c`,
`2*c*x - c^2 ≤ x^2`, with equality if and only if `x = c`.  This is exactly the
`c`-parametrised statement `(x - c)^2 ≥ 0`. -/
theorem rank_trace_c_general (x c : ℝ) :
    2 * c * x - c ^ 2 ≤ x ^ 2 ∧ (2 * c * x - c ^ 2 = x ^ 2 ↔ x = c) := by
  have key : x ^ 2 - (2 * c * x - c ^ 2) = (x - c) ^ 2 := by ring
  refine ⟨by nlinarith [sq_nonneg (x - c)], ?_, ?_⟩
  · intro h
    have h0 : (x - c) ^ 2 = 0 := by rw [← key, h]; ring
    have h1 : x - c = 0 := by simpa using sq_eq_zero_iff.mp h0
    linarith
  · intro h
    subst h
    ring

end method
end Riemann

