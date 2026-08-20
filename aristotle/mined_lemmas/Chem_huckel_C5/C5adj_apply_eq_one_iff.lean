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

lemma C5adj_apply_eq_one_iff (i j : Fin 5) :
    C5adj i j = 1 ↔ (j = i + 1 ∨ i = j + 1) := by
  fin_cases i <;> fin_cases j <;> simp [C5adj]

/-- The characteristic polynomial of the adjacency matrix of `C₅`. -/
