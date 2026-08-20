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

private lemma inner_toEuclideanLin_self {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) (x : EuclideanSpace ℂ q) :
    (inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M x) : ℂ)
      = star (WithLp.ofLp x) ⬝ᵥ ((Mᴴ * M) *ᵥ (WithLp.ofLp x)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [toEuclideanLin_apply', WithLp.ofLp_toLp, Matrix.star_mulVec]
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private lemma dotProduct_conjTranspose_mul_self {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (M : Matrix p q ℂ) (x : EuclideanSpace ℂ q) :
    star (WithLp.ofLp x) ⬝ᵥ ((Mᴴ * M) *ᵥ (WithLp.ofLp x))
      = ((‖(Matrix.toEuclideanLin M x)‖ : ℝ) : ℂ) ^ 2 := by
  rw [← inner_toEuclideanLin_self, inner_self_eq_norm_sq_to_K]
  simp

/-! ### Contractions -/

/-- A matrix `M` is a contraction if `Mᴴ * M ≤ 1`, equivalently if the associated linear map does
not increase the Euclidean norm (see `QI.isContraction_iff`). -/

def IsContraction {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q] (M : Matrix p q ℂ) : Prop :=
  (1 - Mᴴ * M).PosSemidef

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

theorem IsContraction.mul {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] [DecidableEq q]
    [DecidableEq r] {M : Matrix p q ℂ} {N : Matrix q r ℂ} (hM : IsContraction M)
    (hN : IsContraction N) : IsContraction (M * N) := by
  rw [isContraction_iff] at hM hN ⊢
  intro x
  have hcomp : Matrix.toEuclideanLin (M * N) x
      = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) := by
    simp [toEuclideanLin_apply', Matrix.mulVec_mulVec]
  rw [hcomp]
  exact (hM _).trans (hN x)

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
