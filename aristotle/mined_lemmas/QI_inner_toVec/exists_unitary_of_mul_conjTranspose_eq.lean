import Mathlib

/-!
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (density operators, not necessarily
normalized), the fidelity

`F(ρ, σ) = Tr √(√ρ σ √ρ)`

equals the maximum of `|⟪ψ, φ⟫|` over all purifications `ψ` of `ρ` and `φ` of `σ` in
`ℂⁿ ⊗ ℂⁿ ≃ EuclideanSpace ℂ (n × n)`, where the reduced density matrix of a vector `ψ` is
the partial trace over the second tensor factor.

The main result is `QI.uhlmann_fidelity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace QI

variable {n m : Type*} [Fintype n] [Fintype m]

/-! ### Vectorization of matrices -/

/-- The vectorization of a matrix, viewed as a vector of the Hilbert space
`EuclideanSpace ℂ (n × m) ≃ ℂⁿ ⊗ ℂᵐ`. -/

theorem exists_unitary_of_mul_conjTranspose_eq {X Y : Matrix n n ℂ} (h : X * Xᴴ = Y * Yᴴ) :
    ∃ U : Matrix n n ℂ, U ∈ unitary (Matrix n n ℂ) ∧ X = Y * U := by
  classical
  let f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin Yᴴ
  let g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin Xᴴ
  have hinner : ∀ (Z : Matrix n n ℂ) (v : EuclideanSpace ℂ n),
      ⟪Matrix.toEuclideanLin Zᴴ v, Matrix.toEuclideanLin Zᴴ v⟫_ℂ
        = ⟪v, Matrix.toEuclideanLin (Z * Zᴴ) v⟫_ℂ := by
    intro Z v
    nth_rewrite 1 [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [LinearMap.adjoint_inner_left, toEuclideanLin_mul_apply]
  -- `Yᴴ` and `Xᴴ` have the same "norm profile"
  have hnorm : ∀ v, ‖g v‖ = ‖f v‖ := by
    intro v
    have h1 : ⟪g v, g v⟫_ℂ = ⟪f v, f v⟫_ℂ := by
      show ⟪Matrix.toEuclideanLin Xᴴ v, _⟫_ℂ = _
      rw [hinner X v, hinner Y v, h]
    have h2 : ‖g v‖ ^ 2 = ‖f v‖ ^ 2 := by
      have h3 := congrArg Complex.re h1
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
      exact_mod_cast h3
    nlinarith [norm_nonneg (g v), norm_nonneg (f v)]
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro v hv
    simp only [LinearMap.mem_ker] at hv ⊢
    have hv' := hnorm v
    rw [hv, norm_zero] at hv'
    exact norm_eq_zero.mp hv'
  -- the isometry `f v ↦ g v` defined on the range of `f`
  let L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.ker f).liftQ g hker).comp
      (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _)
  have hL₀ : ∀ v : EuclideanSpace ℂ n, L₀ ⟨f v, LinearMap.mem_range_self f v⟩ = g v := by
    intro v
    have hq : f.quotKerEquivRange (Submodule.Quotient.mk v)
        = ⟨f v, LinearMap.mem_range_self f v⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f v)
    show ((LinearMap.ker f).liftQ g hker) (f.quotKerEquivRange.symm _) = g v
    rw [← hq, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hiso : ∀ s : (LinearMap.range f), ‖L₀ s‖ = ‖s‖ := by
    rintro ⟨s, v, rfl⟩
    rw [hL₀ v]
    exact hnorm v
  let L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ n := ⟨L₀, hiso⟩
  -- extend it to an isometry of the whole space
  let T := L.extend
  have hT : ∀ v, T (Matrix.toEuclideanLin Yᴴ v) = Matrix.toEuclideanLin Xᴴ v := by
    intro v
    have := L.extend_apply ⟨f v, LinearMap.mem_range_self f v⟩
    simpa [T, L, hL₀ v] using this
  -- turn the isometry into a unitary matrix
  set Tm : Matrix n n ℂ := Matrix.toEuclideanLin.symm T.toLinearMap with hTmdef
  have hTm : ∀ v, Matrix.toEuclideanLin Tm v = T v := by
    intro v
    rw [hTmdef, LinearEquiv.apply_symm_apply]
    rfl
  have hone : Tmᴴ * Tm = 1 := by
    apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [toEuclideanLin_mul_apply, hTm, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have hv : LinearMap.adjoint (Matrix.toEuclideanLin Tm) (T v) = v := by
      refine ext_inner_right ℂ fun w => ?_
      rw [LinearMap.adjoint_inner_left, hTm]
      exact T.inner_map_map v w
    rw [hv]
    simp
  have hone' : Tm * Tmᴴ = 1 := mul_eq_one_comm.mp hone
  have hXY : Tm * Yᴴ = Xᴴ := by
    apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [toEuclideanLin_mul_apply, hTm]
    exact hT v
  refine ⟨Tmᴴ, ?_, ?_⟩
  · rw [Unitary.mem_iff]
    exact ⟨by simpa [star_eq_conjTranspose] using hone',
      by simpa [star_eq_conjTranspose] using hone⟩
  · rw [← Matrix.conjTranspose_conjTranspose X, ← hXY, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

/-- Polar decomposition: every square matrix is a unitary times its absolute value. -/
