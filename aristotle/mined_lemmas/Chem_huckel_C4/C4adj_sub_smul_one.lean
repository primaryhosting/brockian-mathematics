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

open Polynomial

/-- The adjacency matrix of the cycle graph `C₄` (vertices `0-1-2-3-0`), as a real
`4 × 4` matrix.  This is the Hückel matrix of cyclobutadiene with `α = 0`, `β = 1`. -/

lemma C4adj_sub_smul_one (mu : ℝ) :
    C4adj - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      !![-mu, 1, 0, 1;
         1, -mu, 1, 0;
         0, 1, -mu, 1;
         1, 0, 1, -mu] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4adj]

/-- The characteristic determinant of `C₄`. -/
