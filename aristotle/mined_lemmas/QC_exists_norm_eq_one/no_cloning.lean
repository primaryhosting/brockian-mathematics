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

theorem no_cloning [Nontrivial H] :
    ¬ ∃ (e₀ : H) (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
        ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e₀) = ψ ⊗ₜ[ℂ] ψ := by
  rintro ⟨e₀, U, hU⟩
  replace hU : IsCloner e₀ U := hU
  obtain ⟨ψ, hψ⟩ := exists_norm_eq_one (H := H)
  have hin : inner ℂ ψ ψ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  -- `Complex.I • ψ` is also a unit vector
  have hIψ : ‖(Complex.I • ψ : H)‖ = 1 := by
    rw [norm_smul, hψ]
    simp
  have key := IsCloner.inner_eq hU hψ hIψ
  rw [IsCloner.inner_blank hU] at key
  have hinner : inner ℂ ψ (Complex.I • ψ) = Complex.I := by
    rw [inner_smul_right, hin, mul_one]
  rw [hinner] at key
  have : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  rw [this, mul_one] at key
  -- `key : Complex.I = -1`, which is absurd
  simp [Complex.ext_iff] at key

/-- The no-cloning theorem for a single qubit: there is no unitary on `ℂ² ⊗ ℂ²` that clones
every qubit state. -/
