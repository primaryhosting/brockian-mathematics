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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₄`,
i.e. of cyclobutadiene. -/

lemma C4Matrix_charpoly : C4Matrix.charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [C4Matrix_eq]
  have h : Matrix.charmatrix (!![(0 : ℝ), 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0])
      = !![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.charpoly, h]
  have e1 : (Fin.succAbove (1 : Fin 4) 2) = 3 := by decide
  have e2 : (Fin.succAbove (3 : Fin 4) 2) = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, e1, e2]
  ring

