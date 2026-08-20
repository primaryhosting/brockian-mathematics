/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟪ψ, A ψ⟫` of a (symmetric) operator `A` in the state `ψ`.
For symmetric `A` this complex number is real, so we take its real part. -/

noncomputable def expectation (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := (⟪ψ, A ψ⟫_ℂ).re

/-- The standard deviation (uncertainty) `Δ A = ‖(A - ⟪A⟫) ψ‖` of a symmetric operator `A`
in the state `ψ`. -/
