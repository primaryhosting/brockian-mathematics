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

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/

theorem huckel_C7_spectrum :
    spectrum ℝ C7adj =
      Set.range (fun k : Fin 7 => 2 * Real.cos (2 * Real.pi * (k : ℕ) / 7)) := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C7]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Set.mem_range]
  rw [Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)

end Chem

