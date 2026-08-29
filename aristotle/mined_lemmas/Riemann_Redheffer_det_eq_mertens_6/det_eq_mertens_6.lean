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
open scoped Pointwise

set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

namespace Riemann
namespace Redheffer

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

theorem det_eq_mertens_6 : R6.det = -1 := by
  rw [R6_eq]
  decide

end Redheffer
end Riemann

