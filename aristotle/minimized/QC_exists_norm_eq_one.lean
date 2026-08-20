import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *cloning machine* on a complex inner product space `H` consists of a "blank" state
`e₀ : H` together with a unitary `U` on `H ⊗ H` which maps `ψ ⊗ e₀` to `ψ ⊗ ψ` for every
(normalized) state `ψ`. -/

def IsCloner (e₀ : H) (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)) : Prop :=
  ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e₀) = ψ ⊗ₜ[ℂ] ψ

/-- In a nontrivial normed space there is a vector of norm one. -/

lemma exists_norm_eq_one [Nontrivial H] : ∃ ψ : H, ‖ψ‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨(‖x‖ : ℂ)⁻¹ • x, ?_⟩
  have hx' : ‖x‖ ≠ 0 := by simpa using hx
  rw [norm_smul]
  simp [hx']

/-- A cloner is inner-product preserving on product states: for any two unit states
`ψ, y` we have `⟪ψ, y⟫ * ⟪e₀, e₀⟫ = ⟪ψ, y⟫ ^ 2`. -/

lemma IsCloner.inner_eq {e₀ : H} {U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)} (hU : IsCloner e₀ U)
    {ψ y : H} (hψ : ‖ψ‖ = 1) (hy : ‖y‖ = 1) :
    inner ℂ ψ y * inner ℂ e₀ e₀ = (inner ℂ ψ y) ^ 2 := by
  have h : inner ℂ (U (ψ ⊗ₜ[ℂ] e₀)) (U (y ⊗ₜ[ℂ] e₀)) = inner ℂ (ψ ⊗ₜ[ℂ] e₀) (y ⊗ₜ[ℂ] e₀) :=
    U.inner_map_map _ _
  rw [hU ψ hψ, hU y hy, TensorProduct.inner_tmul, TensorProduct.inner_tmul] at h
  rw [← h]
  ring

/-- For a cloner, the blank state has norm one (equivalently `⟪e₀, e₀⟫ = 1`). -/

lemma IsCloner.inner_blank [Nontrivial H] {e₀ : H} {U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)}
    (hU : IsCloner e₀ U) : inner ℂ e₀ e₀ = (1 : ℂ) := by
  obtain ⟨ψ, hψ⟩ := exists_norm_eq_one (H := H)
  have hin : inner ℂ ψ ψ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have := IsCloner.inner_eq hU hψ hψ
  rw [hin] at this
  simpa using this

/-- **No-cloning theorem.** On a nonzero complex inner product space `H` there is no unitary
`U` on `H ⊗ H` and blank state `e₀` with `U (ψ ⊗ e₀) = ψ ⊗ ψ` for all unit vectors `ψ`. -/
