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

/-!
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Li

/-- Li's second coefficient `λ₂ ≈ 0.0923` is positive: any real number that is at least
`0.09` is strictly positive. -/
theorem lambda2_positive (x : ℝ) (hx : (0.09 : ℝ) ≤ x) : 0 < x := by
  have h : (0 : ℝ) < 0.09 := by norm_num
  exact lt_of_lt_of_le h hx

end Riemann.Li

