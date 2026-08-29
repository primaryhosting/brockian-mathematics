import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`i + 1` divides `j + 1` (using the `0`-indexed `Fin 6` entries), and `0` otherwise. -/

theorem det_R6_eq_mertens :
    Matrix.det R6 = ∑ k ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius k : ℤ) := by
  rw [det_eq_mertens_6, mertens_6]

end Riemann.Redheffer

