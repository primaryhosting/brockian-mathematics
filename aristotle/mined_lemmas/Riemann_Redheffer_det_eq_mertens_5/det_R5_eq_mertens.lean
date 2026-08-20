import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
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

namespace Riemann.Redheffer

/-- The 5×5 Redheffer matrix over `ℤ` (0-indexed): entry `(i, j)` is `1` when `j = 0`
or when `i + 1` divides `j + 1`, and `0` otherwise. -/

theorem det_R5_eq_mertens :
    R5.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_5, mertens_five]

end Riemann.Redheffer

