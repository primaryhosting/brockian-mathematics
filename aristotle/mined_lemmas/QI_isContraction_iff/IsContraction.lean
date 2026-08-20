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


theorem IsContraction.conjTranspose {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {M : Matrix p q ℂ} (h : IsContraction M) : IsContraction Mᴴ := by
  rw [isContraction_iff] at h ⊢
  intro y
  set z : EuclideanSpace ℂ q := Matrix.toEuclideanLin Mᴴ y with hz
  have key : ((‖z‖ : ℝ) : ℂ) ^ 2 = inner ℂ y (Matrix.toEuclideanLin M z) := by
    rw [hz, ← dotProduct_conjTranspose_mul_self Mᴴ y, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [toEuclideanLin_apply', WithLp.ofLp_toLp, Matrix.conjTranspose_conjTranspose,
      Matrix.mulVec_mulVec]
    rw [dotProduct_comm]
  have h1 : ‖z‖ ^ 2 = ‖(inner ℂ y (Matrix.toEuclideanLin M z) : ℂ)‖ := by rw [← key]; simp
  have h2 : ‖(inner ℂ y (Matrix.toEuclideanLin M z) : ℂ)‖ ≤ ‖y‖ * ‖Matrix.toEuclideanLin M z‖ :=
    norm_inner_le_norm _ _
  have h3 : ‖Matrix.toEuclideanLin M z‖ ≤ ‖z‖ := h z
  nlinarith [norm_nonneg z, norm_nonneg y]

/-! ### Polar-type decompositions

Two matrices with the same "Gram matrix" `A * Aᴴ` differ by a unitary (or, in the rectangular
case, contractive) factor on the right.  This is the algebraic heart of Uhlmann's theorem: two
purifications of the same state are related by a unitary on the purifying system. -/

/-- If two linear maps out of a finite-dimensional inner product space have pointwise equal norms,
then the second factors through the first by a linear isometry defined on the range. -/
