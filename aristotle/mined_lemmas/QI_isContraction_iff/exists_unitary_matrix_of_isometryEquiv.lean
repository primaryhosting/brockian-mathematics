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


private lemma exists_unitary_matrix_of_isometryEquiv {n : Type*} [Fintype n] [DecidableEq n]
    (L : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n) :
    ∃ V : Matrix n n ℂ, V ∈ unitary (Matrix n n ℂ) ∧
      ∀ x : n → ℂ, V *ᵥ x = WithLp.ofLp (L (WithLp.toLp 2 x)) := by
  classical
  set V : Matrix n n ℂ := Matrix.toEuclideanLin.symm (L.toLinearEquiv.toLinearMap) with hVdef
  have hV : ∀ x : EuclideanSpace ℂ n, WithLp.toLp 2 (V *ᵥ (WithLp.ofLp x)) = L x := by
    intro x
    have h1 := Matrix.toEuclideanLin.apply_symm_apply (L.toLinearEquiv.toLinearMap)
    have h2 : (Matrix.toEuclideanLin V) x = L x := by rw [hVdef, h1]; rfl
    rw [toEuclideanLin_apply'] at h2
    exact h2
  have hVunit : Vᴴ * V = 1 := by
    ext i j
    have hinner :
        (inner ℂ (L (EuclideanSpace.single i (1:ℂ))) (L (EuclideanSpace.single j (1:ℂ))) : ℂ)
          = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) :=
      L.inner_map_map _ _
    rw [← hV, ← hV] at hinner
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simp only [EuclideanSpace.single, WithLp.ofLp_toLp, Matrix.mulVec_single] at hinner
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
      Pi.star_apply, RCLike.star_def] at *
    simp only [Matrix.col_apply, MulOpposite.op_one, one_smul, Pi.single_apply] at hinner
    have hswap : ∑ x, (starRingEnd ℂ) (V x i) * V x j = ∑ x, V x j * (starRingEnd ℂ) (V x i) := by
      simp [mul_comm]
    rw [hswap, hinner]
    simp [eq_comm]
  refine ⟨V, ?_, fun x => ?_⟩
  · rw [Unitary.mem_iff]
    exact ⟨hVunit, mul_eq_one_comm.mp hVunit⟩
  · have := hV (WithLp.toLp 2 x)
    simpa using congrArg WithLp.ofLp this

/-- The matrix of a linear contraction is a contraction. -/
