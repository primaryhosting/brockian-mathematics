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


private lemma exists_isometryEquiv_comp {n : Type*} [Fintype n]
    {f g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n, ∀ x, L (f x) = g x := by
  obtain ⟨L₁, hL₁⟩ := exists_isometry_on_range hnorm
  refine ⟨L₁.extend.toLinearIsometryEquiv rfl, fun x => ?_⟩
  have hext : L₁.extend ((⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f) : EuclideanSpace ℂ n)
      = L₁ ⟨f x, ⟨x, rfl⟩⟩ := LinearIsometry.extend_apply _ _
  simpa [hL₁ x] using hext

/-- Two linear maps with pointwise equal norms, with possibly different targets, differ by a
linear contraction. -/
