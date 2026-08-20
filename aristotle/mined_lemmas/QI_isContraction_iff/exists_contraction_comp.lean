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


private lemma exists_contraction_comp {n m : Type*} [Fintype n] [Fintype m]
    {f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    {g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m,
      (∀ x, L (f x) = g x) ∧ ∀ x, ‖L x‖ ≤ ‖x‖ := by
  classical
  obtain ⟨L₁, hL₁⟩ := exists_isometry_on_range hnorm
  refine ⟨L₁.toLinearMap ∘ₗ
    ((LinearMap.range f).orthogonalProjection : _ →L[ℂ] _).toLinearMap, fun x => ?_, fun x => ?_⟩
  · have hproj : (LinearMap.range f).orthogonalProjection (f x)
        = (⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f) := by
      simpa using Submodule.orthogonalProjection_mem_subspace_eq_self
        (K := LinearMap.range f) ⟨f x, ⟨x, rfl⟩⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, hproj]
    exact hL₁ x
  · have h1 : ‖L₁ ((LinearMap.range f).orthogonalProjection x)‖
        = ‖((LinearMap.range f).orthogonalProjection x : EuclideanSpace ℂ n)‖ :=
      L₁.norm_map _
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, h1]
    exact Submodule.norm_orthogonalProjection_apply_le _ x

/-- Every surjective linear isometry of `EuclideanSpace ℂ n` is given by a unitary matrix. -/
