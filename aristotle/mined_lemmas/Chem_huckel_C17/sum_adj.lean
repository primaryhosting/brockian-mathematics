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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/

lemma sum_adj (j : Fin 17) (f : Fin 17 → ℂ) :
    ∑ l : Fin 17, A j l * f l = f (j - 1) + f (j + 1) := by
  have hfil : (Finset.univ.filter (fun l : Fin 17 => (SimpleGraph.cycleGraph 17).Adj j l))
      = {j - 1, j + 1} := by
    ext l
    simp [cycle_adj_iff]
  have hne : j - 1 ≠ j + 1 := by revert j; decide
  calc ∑ l : Fin 17, A j l * f l
      = ∑ l ∈ Finset.univ.filter (fun l : Fin 17 => (SimpleGraph.cycleGraph 17).Adj j l), f l := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro l _
        by_cases h : (SimpleGraph.cycleGraph 17).Adj j l <;>
          simp [A, SimpleGraph.adjMatrix_apply, h]
    _ = f (j - 1) + f (j + 1) := by rw [hfil, Finset.sum_pair hne]

