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

lemma charmatrix_C4adj :
    Matrix.charmatrix C4adj =
      !![X, -1, 0, -1;
         -1, X, -1, 0;
         0, -1, X, -1;
         -1, 0, -1, X] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.charmatrix, C4adj, Matrix.diagonal]

/-- The characteristic polynomial of the `C₄` adjacency matrix is the product of
`X - 2 cos (2πk/4)` over `k = 0, 1, 2, 3`; equivalently it is `X⁴ - 4X²`. -/
