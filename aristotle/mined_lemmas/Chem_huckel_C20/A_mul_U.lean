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

lemma A_mul_U : A * U = U * Matrix.diagonal lam := by
  ext i k
  rw [neighbor_sum]
  have h1 : U (i + 1) k = U i k * zeta ((k : ℕ) : ℤ) := by
    have := U_shift i 1 k
    simpa using this
  have h2 : U (i - 1) k = U i k * zeta (-((k : ℕ) : ℤ)) := by
    have h := U_shift (i - 1) 1 k
    rw [sub_add_cancel] at h
    have hz : zeta (((1 : Fin 20) : ℕ) * (k : ℕ)) * zeta (-((k : ℕ) : ℤ)) = 1 := by
      rw [← zeta_add]
      simpa using zeta_zero
    calc U (i - 1) k = U (i - 1) k * (zeta (((1 : Fin 20) : ℕ) * (k : ℕ)) * zeta (-((k : ℕ) : ℤ))) := by
          rw [hz, mul_one]
      _ = (U (i - 1) k * zeta (((1 : Fin 20) : ℕ) * (k : ℕ))) * zeta (-((k : ℕ) : ℤ)) := by ring
      _ = U i k * zeta (-((k : ℕ) : ℤ)) := by rw [← h]
  rw [h1, h2, Matrix.mul_diagonal, lam_eq]
  ring

