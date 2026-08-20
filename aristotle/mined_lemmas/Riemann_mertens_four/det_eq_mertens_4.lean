/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
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

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/

theorem det_eq_mertens_4 : R4.det = mertens 4 ∧ R4.det = -1 := by
  have hdet : R4.det = -1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R4, Matrix.submatrix, Fin.succAbove]
  exact ⟨hdet.trans mertens_four.symm, hdet⟩

end Redheffer
end Riemann

