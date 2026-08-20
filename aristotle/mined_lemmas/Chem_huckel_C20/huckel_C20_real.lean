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

theorem huckel_C20_real :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℝ).charpoly =
      ∏ k : Fin 20, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 20))) := by
  have hmap : ((SimpleGraph.cycleGraph 20).adjMatrix ℝ).map (algebraMap ℝ ℂ)
      = (SimpleGraph.cycleGraph 20).adjMatrix ℂ := by
    ext i j
    by_cases h : (SimpleGraph.cycleGraph 20).Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, h]
  have h := huckel_C20
  rw [← hmap, Matrix.charpoly_map] at h
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  rw [h, Polynomial.map_prod]
  simp

/-- Explicit Hückel molecular orbitals: for each `k`, the vector `j ↦ exp (2 π i j k / 20)` is a
nonzero eigenvector of the adjacency matrix of `C₂₀` with eigenvalue `2 cos (2 π k / 20)`. -/
