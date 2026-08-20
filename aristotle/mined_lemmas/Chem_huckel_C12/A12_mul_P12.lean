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

lemma A12_mul_P12 : A12 * P12 = P12 * D12 := by
  ext i k
  have hrow : (A12 * P12) i k = ∑ u ∈ (SimpleGraph.cycleGraph 12).neighborFinset i, P12 u k := by
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 12) i
      (fun u => P12 u k)
    simpa [A12, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  rw [hrow, SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair (sub_one_ne_add_one i)]
  rw [P12_apply, P12_apply, D12, Matrix.mul_diagonal, P12_apply]
  have h1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have h2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [h1, h2, zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)) (zeta k),
    zeta_add_zeta_neg k]

