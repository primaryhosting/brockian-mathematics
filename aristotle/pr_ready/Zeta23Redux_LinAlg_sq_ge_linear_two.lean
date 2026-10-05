/-!
# Sq Ge Linear Two
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sq_ge_linear_two
Statement: For all real numbers x and c, we have 2 * c * x - c^2 <= x^2. (This is (x - c)^2 >= 0, the c=2 form used in Lemma 3.2.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace Zeta23Redux.LinAlg

/-- For all real `x` and `c`, `2 * c * x - c ^ 2 ≤ x ^ 2`, since this is
equivalent to `(x - c) ^ 2 ≥ 0`. -/
theorem sq_ge_linear_two (x c : ℝ) : 2 * c * x - c ^ 2 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c)]

end Zeta23Redux.LinAlg

