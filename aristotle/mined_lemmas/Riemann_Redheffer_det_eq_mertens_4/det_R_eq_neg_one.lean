/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Redheffer

/-- The `4 × 4` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise (indices are `0`-based). -/

theorem det_R_eq_neg_one : R.det = -1 := by
  simp [R, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  decide

/-- **Redheffer's identity in size 4**: the determinant of the `4 × 4` Redheffer matrix
equals the Mertens function at `4`, namely `-1`. -/
