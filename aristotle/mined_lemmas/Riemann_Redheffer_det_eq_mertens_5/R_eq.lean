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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ`, with `0`-indexed rows and columns:
`R i j = 1` when the column index is `0` (i.e. the entry lies in the first column)
or when `i + 1` divides `j + 1`, and `R i j = 0` otherwise. -/

theorem R_eq : R = !![1, 1, 1, 1, 1;
                      1, 1, 0, 1, 0;
                      1, 0, 1, 0, 0;
                      1, 0, 0, 1, 0;
                      1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The determinant of the `5 × 5` Redheffer matrix equals `-2`. -/
