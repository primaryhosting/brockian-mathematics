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

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/

lemma adjMatrix_mul_Fm : (cycleGraph 11).adjMatrix ℂ * Fm = Fm * Dm := by
  have hnb : ∀ v : Fin 11, (cycleGraph 11).neighborFinset v = {v - 1, v + 1} := by decide
  have hne : ∀ v : Fin 11, v - 1 ≠ v + 1 := by decide
  ext j l
  have hsum : ((cycleGraph 11).adjMatrix ℂ * Fm) j l = Fm (j - 1) l + Fm (j + 1) l := by
    rw [Matrix.mul_apply]
    simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, hnb j,
      Finset.sum_pair (hne j)]
  have hadd : (j + 1).val = (j.val + 1) % 11 := by simp [Fin.val_add]
  have hsub : (j - 1).val = (j.val + 10) % 11 := by
    simp only [Fin.sub_def]
    congr 1
    omega
  have h1 : Fm (j + 1) l = Fm j l * om ^ l.val := by
    simp only [Fm, hadd, om_pow_mod_mul]
    rw [← pow_add]
    congr 1
    ring
  have h2 : Fm (j - 1) l = Fm j l * om ^ (10 * l.val) := by
    simp only [Fm, hsub, om_pow_mod_mul]
    rw [← pow_add]
    congr 1
    ring
  rw [hsum, h1, h2, ← mul_add, add_comm (om ^ (10 * l.val)) (om ^ l.val), om_pow_add_om_pow,
    Dm, Matrix.mul_diagonal]

/-- **Hückel spectrum of the cycle `C₁₁`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph on 11 vertices splits as `∏ (X - 2 cos (2πk/11))`, `k = 0, …, 10`;
i.e. the adjacency eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)`, with multiplicity. -/
