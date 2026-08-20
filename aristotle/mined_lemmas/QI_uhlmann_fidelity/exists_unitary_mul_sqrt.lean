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

theorem exists_unitary_mul_sqrt (M : Matrix n n ℂ) :
    ∃ W ∈ unitaryGroup n ℂ, M = W * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPh : Pᴴ = P := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.1
  have hPP : Pᴴ * P = Mᴴ * M := by
    rw [hPh]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  set mM := Matrix.toEuclideanLin M with hmM
  set mP := Matrix.toEuclideanLin P with hmP
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖mM x‖ = ‖mP x‖ := by
    intro x
    have key : (inner ℂ (mM x) (mM x) : ℂ) = inner ℂ (mP x) (mP x) := by
      rw [inner_toEuclideanLin_self, inner_toEuclideanLin_self, hPP]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]
  have hker : LinearMap.ker mP ≤ LinearMap.ker mM := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L₀ : (LinearMap.range mP) →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.ker mP).liftQ mM hker).comp (mP.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ (x : EuclideanSpace ℂ n) (h : mP x ∈ LinearMap.range mP), L₀ ⟨mP x, h⟩ = mM x := by
    intro x h
    rw [hL₀def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hiso : ∀ y : (LinearMap.range mP), ‖L₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  set L : (LinearMap.range mP) →ₗᵢ[ℂ] EuclideanSpace ℂ n := ⟨L₀, hiso⟩ with hLdef
  set W' := L.extend with hW'
  have hWP : ∀ x : EuclideanSpace ℂ n, W' (mP x) = mM x := by
    intro x
    have h1 : W' ((⟨mP x, ⟨x, rfl⟩⟩ : LinearMap.range mP) : EuclideanSpace ℂ n)
        = L ⟨mP x, ⟨x, rfl⟩⟩ := L.extend_apply _
    simpa [hLdef, hL₀ x] using h1
  set W := Matrix.toEuclideanLin.symm W'.toLinearMap with hWdef
  have hWlin : Matrix.toEuclideanLin W = W'.toLinearMap := by
    rw [hWdef, LinearEquiv.apply_symm_apply]
  refine ⟨W, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.toEuclideanLin.injective
    have h2 : Matrix.toEuclideanLin (star W * W)
        = (LinearMap.adjoint (Matrix.toEuclideanLin W)).comp (Matrix.toEuclideanLin W) := by
      rw [show star W = Wᴴ from rfl, Matrix.toLpLin_mul,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [h2]
    refine LinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, hWlin]
    simp
  · apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLpLin_mul]
    simp only [LinearMap.comp_apply]
    rw [show (Matrix.toEuclideanLin P) x = mP x from rfl, hWlin]
    exact (hWP x).symm

/-- If `A Aᴴ = B Bᴴ` then `A = B U` for some unitary `U`. -/
