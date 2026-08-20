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

theorem no_cloning_qubit :
    ¬ ∃ (e₀ : EuclideanSpace ℂ (Fin 2))
        (U : (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))
              ≃ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))),
        ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e₀) = ψ ⊗ₜ[ℂ] ψ :=
  no_cloning

end

end QC

#print axioms QC.no_cloning
#print axioms QC.no_cloning_qubit

