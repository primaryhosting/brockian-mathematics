/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x y`. -/

noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := ⟪ψ, A ψ⟫_ℂ

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
