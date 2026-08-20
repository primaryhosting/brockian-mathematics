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
