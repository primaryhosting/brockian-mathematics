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

lemma charpoly_adjC :
    ((SimpleGraph.cycleGraph 7).adjMatrix ℂ).charpoly = ∏ k : Fin 7, (X - C (dd k)) := by
  let u : (Matrix (Fin 7) (Fin 7) ℂ)ˣ := ⟨UU, VV, UU_mul_VV, VV_mul_UU⟩
  have hu : ((u⁻¹ : (Matrix (Fin 7) (Fin 7) ℂ)ˣ) : Matrix (Fin 7) (Fin 7) ℂ) = VV := rfl
  have hu' : ((u : Matrix (Fin 7) (Fin 7) ℂ)) = UU := rfl
  have h := Matrix.charpoly_units_conj u (Matrix.diagonal dd)
  rw [hu, hu'] at h
  rw [adjC_eq, h, Matrix.charpoly_diagonal]

end Aux

/-- **Hückel theory for `C₇`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₇` is `∏_{k=0}^{6} (X - 2 cos (2πk/7))`; i.e. the adjacency eigenvalues of `C₇`
are `2 cos (2πk/7)` for `k = 0, …, 6`. -/
