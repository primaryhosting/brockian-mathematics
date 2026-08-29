import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
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

namespace Riemann
namespace Redheffer

/-- The 3×3 Redheffer matrix: `R i j = 1` when `j = 0` or `(i+1) ∣ (j+1)`
(with 0-indexed `Fin 3`), and `0` otherwise.  Its rows are
`(1,1,1)`, `(1,1,0)`, `(1,0,1)`. -/

theorem det_eq_mertens_sum_3 :
    R.det = ∑ n ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius n : ℤ) := by
  rw [mertens_three, det_eq_mertens_3]

end Redheffer
end Riemann

