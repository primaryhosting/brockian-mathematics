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

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma B6_mul_B6 : B6 * B6 = (5 : ℝ) • B6 - (4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.smul_apply, Matrix.sub_apply] <;>
      norm_num

/-- Every eigenvalue of the adjacency matrix of `C₆` is a root of `X⁴ - 5X² + 4`. -/
