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

theorem charpoly_A : A.charpoly = ∏ k : Fin 20, (X - C (lam k)) := by
  set M : (Matrix (Fin 20) (Fin 20) ℂ)ˣ := Matrix.nonsingInvUnit U isUnit_det_U with hM
  have hMval : (M : Matrix (Fin 20) (Fin 20) ℂ) = U := rfl
  have hMinv : ((M⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = U⁻¹ := rfl
  have hA : A = (M : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal lam
      * ((M⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
    rw [hMval, hMinv, ← A_mul_U, Matrix.mul_assoc, Matrix.mul_nonsing_inv U isUnit_det_U,
      Matrix.mul_one]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for C₂₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` factors as `∏_{k=0}^{19} (X - 2 cos (2 π k / 20))`; equivalently, the adjacency
eigenvalues of `C₂₀` are `2 cos (2 π k / 20)` for `k = 0, …, 19` (listed with multiplicity). -/
