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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix: entry `(i, j)` is `1` when `j = 0` (first column)
or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

theorem R6_eq :
    R6 = !![1,1,1,1,1,1;
            1,1,0,1,0,1;
            1,0,1,0,0,1;
            1,0,0,1,0,0;
            1,0,0,0,1,0;
            1,0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R6] <;> decide

theorem det_eq_mertens_6 : R6.det = -1 := by
  rw [R6_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three]
  norm_num

end Riemann.Redheffer

