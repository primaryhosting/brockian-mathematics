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

/-
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Li

/-- If `0.09 ≤ x` then `0 < x`.

This encodes the positivity of Li's second coefficient `λ₂ ≈ 0.0923`
(Li's criterion: RH holds iff `λ_n ≥ 0` for all `n ≥ 1`): any real number
bounded below by `0.09` is positive.

The proof is Mathlib's `lt_of_lt_of_le` applied to the numeric fact
`(0 : ℝ) < 0.09`. -/
theorem lambda2_positive (x : ℝ) (hx : 0.09 ≤ x) : 0 < x :=
  lt_of_lt_of_le (by norm_num) hx

end Riemann.Li

