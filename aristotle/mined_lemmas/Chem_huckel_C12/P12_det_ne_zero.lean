import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

lemma P12_det_ne_zero : P12.det ≠ 0 := by
  rw [P12, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have : om ^ (j : ℕ) ≠ om ^ (i : ℕ) := by
    intro h
    have := om_primitiveRoot.pow_inj j.isLt i.isLt h
    exact absurd (Fin.ext this) (ne_of_gt hij)
  exact sub_ne_zero.mpr this

