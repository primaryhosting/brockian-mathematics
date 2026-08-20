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


theorem isContraction_iff {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) :
    IsContraction M ↔ ∀ x : EuclideanSpace ℂ q, ‖Matrix.toEuclideanLin M x‖ ≤ ‖x‖ := by
  have hherm : (1 - Mᴴ * M).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hself : ∀ x : EuclideanSpace ℂ q,
      star (WithLp.ofLp x) ⬝ᵥ ((1 - Mᴴ * M) *ᵥ (WithLp.ofLp x))
        = (((‖x‖ : ℝ) ^ 2 - ‖Matrix.toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_conjTranspose_mul_self M x]
    have h2 : star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
      simpa using dotProduct_conjTranspose_mul_self (1 : Matrix q q ℂ) x
    rw [h2]; push_cast; ring
  constructor
  · intro h x
    have h1 := h.dotProduct_mulVec_nonneg (WithLp.ofLp x)
    rw [hself x] at h1
    have h2 : (0 : ℝ) ≤ ‖x‖ ^ 2 - ‖Matrix.toEuclideanLin M x‖ ^ 2 := by exact_mod_cast h1
    nlinarith [norm_nonneg (Matrix.toEuclideanLin M x), norm_nonneg x]
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun x => ?_)
    have hx := hself (WithLp.toLp 2 x)
    rw [hx]
    have h1 := h (WithLp.toLp 2 x)
    have h2 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ q)‖ ^ 2
        - ‖Matrix.toEuclideanLin M (WithLp.toLp 2 x)‖ ^ 2 := by
      nlinarith [norm_nonneg (Matrix.toEuclideanLin M (WithLp.toLp 2 x)),
        norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ q)]
    exact_mod_cast h2

