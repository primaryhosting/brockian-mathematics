/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

theorem inner_isSelfAdjoint_left {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (x y : H) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  conv_lhs => rw [show A = ContinuousLinearMap.adjoint A from by
    rw [← ContinuousLinearMap.star_eq_adjoint, hA.star_eq]]
  exact ContinuousLinearMap.adjoint_inner_left A y x

/-- Expectation values of self-adjoint operators are real. -/
