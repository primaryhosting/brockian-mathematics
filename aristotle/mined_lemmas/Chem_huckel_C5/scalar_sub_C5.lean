import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₅`, i.e. the Hückel matrix of
cyclopentadienyl (with `α = 0`, `β = 1`). -/

lemma scalar_sub_C5 (t : ℝ) :
    (Matrix.scalar (Fin 5) t - C5)
      = !![t,-1,0,0,-1; -1,t,-1,0,0; 0,-1,t,-1,0; 0,0,-1,t,-1; -1,0,0,-1,t] := by
  rw [C5_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

/-- The characteristic polynomial of the adjacency matrix of `C₅`,
evaluated at `t`, is `t⁵ - 5t³ + 5t - 2`. -/
