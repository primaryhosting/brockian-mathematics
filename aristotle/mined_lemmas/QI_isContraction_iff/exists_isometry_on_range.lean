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


private lemma exists_isometry_on_range {n m : Type*} [Fintype n] [Fintype m]
    {f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    {g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m,
      ∀ x : EuclideanSpace ℂ n, L ⟨f x, ⟨x, rfl⟩⟩ = g x := by
  classical
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hgx : ‖g x‖ = 0 := by rw [hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hgx
  set L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    (Submodule.liftQ _ g hker) ∘ₗ
      (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ x : EuclideanSpace ℂ n, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hsymm : f.quotKerEquivRange.symm ⟨f x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      apply f.quotKerEquivRange.injective
      simp
    simp [hL₀def, hsymm]
  have hnormL₀ : ∀ y : (LinearMap.range f), ‖L₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  exact ⟨⟨L₀, hnormL₀⟩, hL₀⟩

/-- Two endomorphisms of a finite-dimensional inner product space with pointwise equal norms
differ by a surjective linear isometry. -/
