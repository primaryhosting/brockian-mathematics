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

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma adj8_mulVec {α : Type*} [NonAssocSemiring α] (v : Fin 8 → α) (i : Fin 8) :
    ((SimpleGraph.cycleGraph 8).adjMatrix α *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset (n := 6),
    Finset.sum_pair]
  revert i; decide

