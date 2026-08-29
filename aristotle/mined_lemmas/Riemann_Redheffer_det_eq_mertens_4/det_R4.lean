/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
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

/-- The `4 × 4` Redheffer matrix: with `0`-based indices `i j : Fin 4`,
`R4 i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

theorem det_R4 : R4.det = -1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R4, Matrix.submatrix_apply,
    Fin.succAbove, Matrix.of_apply]

/-- The Mertens function at `4`: `μ 1 + μ 2 + μ 3 + μ 4 = 1 - 1 - 1 + 0 = -1`. -/
