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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/

lemma L5_mul_swap : L5 * (R5.submatrix (Equiv.swap 1 2) id) = U5 := by
  rw [R5_eq]
  have h : ((!![1, 1, 1, 1, 1;
                1, 1, 0, 1, 0;
                1, 0, 1, 0, 0;
                1, 0, 0, 1, 0;
                1, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) ℤ).submatrix (Equiv.swap 1 2) id) =
      !![1, 1, 1, 1, 1;
         1, 0, 1, 0, 0;
         1, 1, 0, 1, 0;
         1, 0, 0, 1, 0;
         1, 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L5, U5, Matrix.mul_apply, Fin.sum_univ_five]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function value
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
