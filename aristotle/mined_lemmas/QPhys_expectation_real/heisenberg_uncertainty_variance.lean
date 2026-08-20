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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation values of a symmetric operator are real. -/

theorem heisenberg_uncertainty_variance (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    Real.sqrt (variance A psi) * Real.sqrt (variance B psi) ≥ hbar / 2 := by
  rw [variance_eq_norm_centered_sq A hA psi hpsi, variance_eq_norm_centered_sq B hB psi hpsi,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact heisenberg_uncertainty A B hA hB hbar psi hpsi hcomm

#print axioms QPhys.heisenberg_uncertainty_variance

end QPhys

