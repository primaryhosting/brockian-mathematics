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

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

theorem F_isUnit : IsUnit F := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, F, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have := w_primitive.pow_inj j.isLt i.isLt h
  exact absurd (Fin.ext this) (Fin.ne_of_gt hj)

