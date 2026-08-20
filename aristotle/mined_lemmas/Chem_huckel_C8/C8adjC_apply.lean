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

theorem C8adjC_apply (i j : Fin 8) :
    C8adjC i j = if i - j = 1 ∨ i - j = -1 then 1 else 0 := by
  rw [C8adjC, Matrix.map_apply, cycleGraph_adjMatrix_eq_circulant]
  simp only [Matrix.circulant_apply]
  split <;> simp

/-! ### The eighth roots of unity -/

