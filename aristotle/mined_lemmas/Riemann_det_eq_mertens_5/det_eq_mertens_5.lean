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

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry `(i, j)` is `1`
when `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

theorem det_eq_mertens_5 : R.det = -2 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, R, Matrix.of_apply, Fin.succAbove]
  norm_num [Fin.lt_def]
  decide

/-- The Mertens function value `M(5)`, written out as the sum of `μ(n)` for `n ≤ 5`. -/
