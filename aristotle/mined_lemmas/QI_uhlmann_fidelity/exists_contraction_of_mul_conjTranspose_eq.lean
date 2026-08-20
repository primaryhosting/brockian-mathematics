/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem exists_contraction_of_mul_conjTranspose_eq {A : Matrix n m ℂ} {R : Matrix n n ℂ}
    (h : A * Aᴴ = R * Rᴴ) :
    ∃ V : Matrix n m ℂ, A = R * V ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin V z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Vᴴ y‖ ≤ ‖y‖) := by
  set mA := Matrix.toEuclideanLin Aᴴ with hmA
  set mR := Matrix.toEuclideanLin Rᴴ with hmR
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖mA x‖ = ‖mR x‖ := by
    intro x
    have key : (inner ℂ (mA x) (mA x) : ℂ) = inner ℂ (mR x) (mR x) := by
      rw [hmA, hmR, inner_toEuclideanLin_self, inner_toEuclideanLin_self]
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [h]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]
  have hker : LinearMap.ker mR ≤ LinearMap.ker mA := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L₀ : (LinearMap.range mR) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker mR).liftQ mA hker).comp (mR.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ (x : EuclideanSpace ℂ n) (hx : mR x ∈ LinearMap.range mR),
      L₀ ⟨mR x, hx⟩ = mA x := by
    intro x hx
    rw [hL₀def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hiso : ∀ y : (LinearMap.range mR), ‖L₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  set T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m :=
    L₀.comp (LinearMap.range mR).orthogonalProjection.toLinearMap with hTdef
  have hT : ∀ x : EuclideanSpace ℂ n, T (mR x) = mA x := by
    intro x
    have hmem : mR x ∈ LinearMap.range mR := ⟨x, rfl⟩
    have hproj : (LinearMap.range mR).orthogonalProjection (mR x) = ⟨mR x, hmem⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self ⟨mR x, hmem⟩
    rw [hTdef]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hproj]
    exact hL₀ x hmem
  have hTnorm : ∀ y : EuclideanSpace ℂ n, ‖T y‖ ≤ ‖y‖ := by
    intro y
    rw [hTdef]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hiso]
    exact (LinearMap.range mR).norm_orthogonalProjection_apply_le y
  set Vc := Matrix.toEuclideanLin.symm T with hVcdef
  have hVclin : Matrix.toEuclideanLin Vc = T := by rw [hVcdef, LinearEquiv.apply_symm_apply]
  have hadj : Matrix.toEuclideanLin (Vcᴴ) = LinearMap.adjoint T := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hVclin]
  refine ⟨Vcᴴ, ?_, ?_, ?_⟩
  · have hAeq : Aᴴ = Vc * Rᴴ := by
      apply Matrix.toEuclideanLin.injective
      refine LinearMap.ext fun x => ?_
      rw [Matrix.toLpLin_mul]
      simp only [LinearMap.comp_apply]
      rw [hVclin]
      exact (hT x).symm
    have hc := congrArg Matrix.conjTranspose hAeq
    simpa [Matrix.conjTranspose_mul] using hc
  · intro u
    rw [hadj]
    set a := LinearMap.adjoint T u with hadef
    have h1 : ‖a‖ ^ 2 = RCLike.re (inner ℂ a a : ℂ) := norm_sq_eq_re_inner (𝕜 := ℂ) a
    have h2 : (inner ℂ a a : ℂ) = inner ℂ (T a) u := by
      rw [hadef, LinearMap.adjoint_inner_right]
    have h3 : RCLike.re (inner ℂ (T a) u : ℂ) ≤ ‖a‖ * ‖u‖ := by
      calc RCLike.re (inner ℂ (T a) u : ℂ) ≤ ‖(inner ℂ (T a) u : ℂ)‖ := RCLike.re_le_norm _
        _ ≤ ‖T a‖ * ‖u‖ := norm_inner_le_norm _ _
        _ ≤ ‖a‖ * ‖u‖ := mul_le_mul_of_nonneg_right (hTnorm a) (norm_nonneg u)
    rw [h2] at h1
    nlinarith [norm_nonneg a, norm_nonneg u]
  · intro y
    rw [Matrix.conjTranspose_conjTranspose, hVclin]
    exact hTnorm y

omit [DecidableEq n] in
/-- The Hilbert–Schmidt norm of a matrix as the sum of the squared norms of its columns. -/
