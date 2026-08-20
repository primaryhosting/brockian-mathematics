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
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open Matrix

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

theorem det_R6_eq_mertens_sum :
    R6.det = ∑ n ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_6, mertens_six]

/-- The Mertens value splits as `M(6) = M(5) + μ(6) = -2 + 1 = -1`. -/
