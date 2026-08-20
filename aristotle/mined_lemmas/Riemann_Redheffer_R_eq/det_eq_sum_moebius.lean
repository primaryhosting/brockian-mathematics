import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open ArithmeticFunction

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`(i+1) ∣ (j+1)` (divisibility of the 1-based indices), and `0` otherwise. -/

theorem det_eq_sum_moebius :
    R.det = ∑ n ∈ Finset.Icc 1 4, (moebius n : ℤ) := by
  rw [det_eq_mertens_4, sum_moebius_Icc_four]

end Riemann.Redheffer

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

