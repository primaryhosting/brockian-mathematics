import Mathlib

/-!
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
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

namespace Riemann.Robin

open ArithmeticFunction

/-- `σ₁(16) = 1 + 2 + 4 + 8 + 16 = 31`. -/

lemma sigma_one_sixteen : ArithmeticFunction.sigma 1 16 = 31 := by
  simp [ArithmeticFunction.sigma_one_apply]
  decide

/-- `σ₁(9) = 1 + 3 + 9 = 13`. -/
