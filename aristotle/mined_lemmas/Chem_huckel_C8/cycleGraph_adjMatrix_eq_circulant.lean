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

/-- A primitive 8-th root of unity. -/

theorem cycleGraph_adjMatrix_eq_circulant :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℝ)
      = Matrix.circulant (fun i : Fin 8 => if i = 1 ∨ i = -1 then (1 : ℝ) else 0) := by
  have key : ∀ i j : Fin 8, (j = 1 + i) ↔ (i = -1 + j) := by
    intro i j
    constructor <;> (rintro rfl; abel)
  ext i j
  simp [SimpleGraph.adjMatrix, Matrix.circulant, SimpleGraph.cycleGraph_adj,
    sub_eq_iff_eq_add, key]

/-- The adjacency matrix of `C₈`, viewed over `ℂ`. -/
