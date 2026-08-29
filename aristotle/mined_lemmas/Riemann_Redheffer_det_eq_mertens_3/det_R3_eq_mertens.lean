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

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The 3×3 Redheffer matrix: `R i j = 1` if `j = 0` (first column) or
`(i+1) ∣ (j+1)`, and `0` otherwise (using 0-indexed `Fin 3`). -/

theorem det_R3_eq_mertens :
    R3.det = (ArithmeticFunction.moebius 1 : ℤ) + ArithmeticFunction.moebius 2 +
      ArithmeticFunction.moebius 3 := by
  rw [det_eq_mertens_3, mertens_three]

end Redheffer
end Riemann

