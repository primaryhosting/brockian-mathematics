import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with finite-dimensional quantum systems, a state on `ℂⁿ` being described by a positive
semidefinite matrix `ρ : Matrix n n ℂ`.  Its fidelity with a second state `σ` is

`F(ρ, σ) = Tr √(√ρ σ √ρ)`,

which is `QI.fidelity`.

A *purification* of `ρ` in the doubled system `ℂⁿ ⊗ ℂⁿ` is a vector `u : n × n → ℂ` whose reduced
density matrix (partial trace over the second factor) is `ρ`; this is `QI.reducedDensity`.
`QI.uhlmann_fidelity` is Uhlmann's theorem: `F(ρ, σ)` is the *greatest* value of the overlap
`|⟪u, v⟫|` as `u` ranges over the purifications of `ρ` and `v` over those of `σ`.

The proof goes through the polar decomposition of a matrix (`QI.exists_unitary_polar`, proved
here from scratch by extending a linear isometry defined on a subspace) and the variational
characterisation of the trace norm (`QI.isGreatest_traceNorm`).
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

/-! ### An auxiliary extension lemma for linear isometries -/

/-- If `f g : E →ₗ[ℂ] E` satisfy `‖g x‖ = ‖f x‖` for all `x`, then there is a linear isometry `V`
of `E` with `V ∘ f = g`.  This is the key step in the polar decomposition. -/

theorem exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, M = CFC.sqrt (M * Mᴴ) * U := by
  set E := EuclideanSpace ℂ n
  set P := CFC.sqrt (M * Mᴴ) with hPdef
  have hMM : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  have hP : P.PosSemidef := (CFC.sqrt_nonneg (M * Mᴴ)).posSemidef
  have hPP : P * P = M * Mᴴ := CFC.sqrt_mul_sqrt_self _ (ha := hMM.nonneg)
  have hPh : Pᴴ = P := hP.isHermitian
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) with hT
  set p : E →L[ℂ] E := T P with hp
  set a : E →L[ℂ] E := T M with ha
  have hTM : T Mᴴ = star a := by rw [ha, ← map_star, Matrix.star_eq_conjTranspose]
  have hstar : star p * p = a * star a := by
    rw [hp, ha, ← map_star, ← map_star, ← map_mul, ← map_mul]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hPh, hPP]
  have hnormeq : ∀ x : E, ‖(star a) x‖ = ‖p x‖ := by
    intro x
    have h1 : ⟪(star p * p) x, x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have h2 : ⟪(a * star a) x, x⟫_ℂ = ⟪(star a) x, (star a) x⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply]
      have h := ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ) (star a) x ((star a) x)
      rw [ContinuousLinearMap.star_eq_adjoint] at h ⊢
      rwa [ContinuousLinearMap.adjoint_adjoint] at h
    have h3 : ⟪(star a) x, (star a) x⟫_ℂ = ⟪p x, p x⟫_ℂ := by rw [← h1, ← h2, hstar]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖(star a) x‖ ^ 2 = ‖p x‖ ^ 2 := by exact_mod_cast h3
    nlinarith [norm_nonneg ((star a) x), norm_nonneg (p x)]
  obtain ⟨V, hV⟩ := exists_linearIsometry_comp_eq (E := E) p.toLinearMap (star a).toLinearMap
    (by intro x; exact hnormeq x)
  simp only [ContinuousLinearMap.coe_coe] at hV
  set e : E ≃ₗᵢ[ℂ] E := V.toLinearIsometryEquiv rfl with he
  set u : E →L[ℂ] E := (e : E →L[ℂ] E) with hu
  have hue : ∀ x, u x = V x := fun x =>
    congrFun (LinearIsometry.coe_toLinearIsometryEquiv V rfl) x
  have huu : u ∈ unitary (E →L[ℂ] E) := by
    constructor
    · ext x; simp [hu, LinearIsometryEquiv.star_eq_symm]
    · ext x; simp [hu, LinearIsometryEquiv.star_eq_symm]
  have hup : u * p = star a := by
    ext x
    rw [ContinuousLinearMap.mul_apply, hue, hV x]
  set W : Matrix n n ℂ := T.symm u with hW
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', hW, ← map_star, ← map_mul, huu.1, map_one]
  have hWP : W * P = Mᴴ := by
    have h6 : W * P = T.symm (u * p) := by
      rw [map_mul, hW, hp, T.symm_apply_apply]
    rw [h6, hup, ← hTM, T.symm_apply_apply]
  refine ⟨Wᴴ, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hWu
  · have h7 := congrArg Matrix.conjTranspose hWP
    rw [Matrix.conjTranspose_mul, hPh, Matrix.conjTranspose_conjTranspose] at h7
    exact h7.symm

/-! ### Cauchy–Schwarz for the Frobenius inner product -/

omit [DecidableEq n] in
