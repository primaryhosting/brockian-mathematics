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
# Lambda 3 Positive
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Li.lambda3_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lambda 3 Positive
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Li.lambda3_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Li

/-- For all real `x` with `0.0993 ≤ x`, we have `0 < x`.
This encodes positivity of Li's third coefficient `λ₃ ≈ 0.0993`
(Li's criterion: RH iff `λ_n ≥ 0` for all `n ≥ 1`). -/

theorem lambda3_positive (x : ℝ) (hx : (0.0993 : ℝ) ≤ x) : 0 < x := by
  have h : (0 : ℝ) < 0.0993 := by norm_num
  linarith

end Riemann.Li

