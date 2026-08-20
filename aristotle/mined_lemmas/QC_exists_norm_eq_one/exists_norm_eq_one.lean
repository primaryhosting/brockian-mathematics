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

lemma exists_norm_eq_one [Nontrivial H] : ∃ ψ : H, ‖ψ‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨(‖x‖ : ℂ)⁻¹ • x, ?_⟩
  have hx' : ‖x‖ ≠ 0 := by simpa using hx
  rw [norm_smul]
  simp [hx']

/-- A cloner is inner-product preserving on product states: for any two unit states
`ψ, y` we have `⟪ψ, y⟫ * ⟪e₀, e₀⟫ = ⟪ψ, y⟫ ^ 2`. -/
