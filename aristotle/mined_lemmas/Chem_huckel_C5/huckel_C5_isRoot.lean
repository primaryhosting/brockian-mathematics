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

theorem huckel_C5_isRoot (k : Fin 5) :
    C5adj.charpoly.IsRoot (2 * Real.cos (2 * π * (k : ℕ) / 5)) := by
  rw [huckel_C5]
  simp only [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨k, Finset.mem_univ k, by simp⟩

/-- Consequence: the roots of the characteristic polynomial of `C₅` are precisely the
numbers `2·cos(2πk/5)`, `k = 0,…,4`. -/
