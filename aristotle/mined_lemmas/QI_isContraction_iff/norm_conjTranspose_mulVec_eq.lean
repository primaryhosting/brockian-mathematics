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
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (in particular, for density matrices of
a finite dimensional quantum system) the *fidelity* is

`F(ρ, σ) = tr √(√ρ σ √ρ)`.

A vector of `ℂ^n ⊗ ℂ^m` is encoded here as a matrix `A : Matrix n m ℂ`; its reduced density
matrix on the first factor is `A * Aᴴ`, and the overlap of the vectors encoded by `A` and `B` is
`tr (Aᴴ * B)`.  Thus `A` is a *purification* of `ρ` exactly when `A * Aᴴ = ρ`.

**Uhlmann's theorem** (`QI.uhlmann_fidelity`) states that `F(ρ, σ)` is the maximum of
`‖tr (Aᴴ * B)‖` over all purifications `A` of `ρ` and `B` of `σ`.  The maximum is attained already
with a purifying system of the same dimension as the original one, and
`QI.overlap_le_fidelity` shows that no larger purifying system can do better.

The main ingredients proved along the way are a polar-type decomposition of matrices
(`QI.exists_unitary_mul_of_mul_conjTranspose_eq` and its rectangular contraction version), the
Hilbert–Schmidt Cauchy–Schwarz inequality (`QI.abs_trace_conjTranspose_mul_le`) and the bound
`‖tr (P * U)‖ ≤ tr P` for `P` positive semidefinite and `U` a contraction
(`QI.abs_trace_mul_contraction_le`).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Norms of matrix-vector products -/


private lemma norm_conjTranspose_mulVec_eq {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (A : Matrix n m ℂ) (R : Matrix n n ℂ) (h : A * Aᴴ = R * Rᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Rᴴ x‖ := by
  have h1 := dotProduct_conjTranspose_mul_self Aᴴ x
  have h2 := dotProduct_conjTranspose_mul_self Rᴴ x
  rw [Matrix.conjTranspose_conjTranspose, h] at h1
  rw [Matrix.conjTranspose_conjTranspose] at h2
  rw [h2] at h1
  have h3 : ‖Matrix.toEuclideanLin Rᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 := by
    exact_mod_cast h1
  nlinarith [norm_nonneg (Matrix.toEuclideanLin Aᴴ x), norm_nonneg (Matrix.toEuclideanLin Rᴴ x)]

/-- **Polar-type decomposition.** If `A * Aᴴ = R * Rᴴ` for square matrices `A` and `R`, then
`A = R * W` for some unitary `W`. -/
