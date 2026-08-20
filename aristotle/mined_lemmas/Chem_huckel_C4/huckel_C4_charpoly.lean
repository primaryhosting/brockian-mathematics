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

theorem huckel_C4_charpoly :
    C4adj.charpoly = ∏ k : Fin 4, (X - C (huckelEigenvalue k)) := by
  have hdet : C4adj.charpoly = X ^ 4 - 4 * X ^ 2 := by
    rw [Matrix.charpoly, charmatrix_C4adj]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc]
    ring
  rw [hdet, Fin.prod_univ_four, huckelEigenvalue_zero, huckelEigenvalue_one,
    huckelEigenvalue_two, huckelEigenvalue_three]
  simp only [map_zero, map_neg, map_ofNat, sub_zero]
  ring

/-- **Hückel theory for cyclobutadiene.**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₄` if and only if `μ = 2 cos (2πk/4)` for some
`k ∈ {0, 1, 2, 3}`. -/
