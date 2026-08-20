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

open Polynomial

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl,
with `α = 0`, `β = 1`): vertices `0,1,2,3,4` in a cycle, `A i j = 1` iff `i` and `j`
are adjacent along the cycle. -/

lemma charpoly_C5adj : C5adj.charpoly = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove, Matrix.diagonal_apply, Matrix.submatrix_apply, C5adj]
  ring

