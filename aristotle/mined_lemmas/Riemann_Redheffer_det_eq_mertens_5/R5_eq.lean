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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/

theorem R5_eq :
    R5 = !![1, 1, 1, 1, 1;
            1, 1, 0, 1, 0;
            1, 0, 1, 0, 0;
            1, 0, 0, 1, 0;
            1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R5]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function value
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
