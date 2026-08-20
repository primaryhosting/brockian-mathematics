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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

theorem spectrum_adjC9 :
    spectrum ℝ adjC9 = Set.range (fun k : Fin 9 => 2 * Real.cos (2 * Real.pi * k / 9)) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C9]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]
  exact exists_congr (fun _ => by constructor <;> intro h <;> linarith)

end Chem

