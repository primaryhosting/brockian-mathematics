/-
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
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

namespace Riemann
namespace Li

/-- **Lambda 2 positive.** Any real number bounded below by `0.09` is positive.

This encodes the positivity of Li's second coefficient `λ₂ ≈ 0.0923` (Li's criterion:
RH holds iff `λ n ≥ 0` for all `n ≥ 1`): from the numerical lower bound `0.09 ≤ λ₂`
one concludes `0 < λ₂`. -/
theorem lambda2_positive (x : ℝ) (hx : (0.09 : ℝ) ≤ x) : 0 < x := by
  have h : (0 : ℝ) < 0.09 := by norm_num
  exact lt_of_lt_of_le h hx

end Li
end Riemann

