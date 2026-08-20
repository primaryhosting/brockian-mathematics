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

lemma Pv_det_ne_zero : Pv.det ≠ 0 := by
  rw [Pv, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  exact absurd (Fin.ext (om_prim.pow_inj j.isLt i.isLt h)) (ne_of_gt hj)

/-- The complex adjacency matrix is conjugated to the diagonal matrix of the numbers
`2 cos (2πk/8)` by the Fourier matrix. -/
