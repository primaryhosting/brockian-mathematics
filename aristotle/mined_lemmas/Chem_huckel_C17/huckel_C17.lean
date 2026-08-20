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

theorem huckel_C17 :
    ((SimpleGraph.cycleGraph 17).adjMatrix ℝ).charpoly
        = ∏ k : Fin 17, (X - C (2 * Real.cos (2 * Real.pi * k.val / 17)))
      ∧ spectrum ℝ ((SimpleGraph.cycleGraph 17).adjMatrix ℝ)
        = {x : ℝ | ∃ k : Fin 17, x = 2 * Real.cos (2 * Real.pi * k.val / 17)} := by
  refine ⟨charpoly_Areal, ?_⟩
  ext x
  rw [Set.mem_setOf_eq, show ((SimpleGraph.cycleGraph 17).adjMatrix ℝ) = Areal from rfl,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, charpoly_Areal]
  simp [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, huckelEigen]

end Chem

