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
# Hückel theory for the cycle C₂₀

The adjacency eigenvalues of the cycle graph `C₂₀` are `2 * cos (2 π k / 20)`, `k = 0, …, 19`.

We prove this by explicitly diagonalizing the adjacency matrix with the discrete Fourier
transform matrix `U i k = ζ (i * k)`, where `ζ m = exp (2 π i m / 20)`.
-/

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- `ζ m = exp (2 π i m / 20)`, a 20-th root of unity raised to the power `m`. -/

lemma neighbor_sum (i k : Fin 20) :
    (A * U) i k = U (i - 1) k + U (i + 1) k := by
  have hne : i - 1 ≠ i + 1 := by
    intro hc
    have h1 : (i - 1) + 1 = (i + 1) + 1 := by rw [hc]
    rw [sub_add_cancel] at h1
    have hone : (1 : Fin 20) + 1 = 2 := by decide
    have h2 : i + 2 = i + 0 := by
      rw [add_zero]
      conv_rhs => rw [h1]
      rw [add_assoc, hone]
    have h3 : (2 : Fin 20) = 0 := add_left_cancel h2
    exact absurd h3 (by decide)
  have h2 : (A * U) i k
      = ((SimpleGraph.cycleGraph 20).adjMatrix ℂ *ᵥ (fun j => U j k)) i := by
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h2, SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (20 : ℕ) = 18 + 2 from rfl] at *
  rw [SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]

