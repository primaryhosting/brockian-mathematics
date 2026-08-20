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

theorem spectrum_C8 :
    spectrum ℝ ((SimpleGraph.cycleGraph 8).adjMatrix ℝ)
      = Set.range (fun k : Fin 8 => 2 * Real.cos (2 * Real.pi * k.val / 8)) := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C8]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero, Set.mem_range]
  exact exists_congr fun _ => eq_comm

end Chem

