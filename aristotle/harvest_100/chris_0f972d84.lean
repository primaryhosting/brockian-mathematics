import Mathlib
/-!
# Sq Ge Linear
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sq_ge_linear
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- For all real numbers `x` and `c`, `c * x - c ^ 2 / 4 ≤ x ^ 2`.

This is exactly the statement `(x - c / 2) ^ 2 ≥ 0` rearranged; the scalar shadow of the
rank-trace inequality (Lemma 3.2).

Mathlib has no lemma in exactly this form (`exact?` finds none), but the equivalent AM-GM shape
`four_mul_le_sq_add : 4 * a * b ≤ (a + b) ^ 2` (with `a = c/2`, `b = x`) nearly closes it. The
proof below simply uses `sq_nonneg (x - c / 2)`. -/
theorem sq_ge_linear (x c : ℝ) : c * x - c ^ 2 / 4 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c / 2)]

end Zeta23Redux.LinAlg

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

