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

theorem heisenberg_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (hbar : ℝ)
    (hcomm : ∀ x : H, A (B x) - B (A x) = (Complex.I * hbar) • x)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    spread A ψ * spread B ψ ≥ hbar / 2 := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hcomm' : ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ = Complex.I * hbar := by
    rw [hcomm ψ, inner_smul_right, hψψ, mul_one]
  have h := robertson_uncertainty A B hA hB ψ hψ
  rw [hcomm'] at h
  have : ‖Complex.I * (hbar : ℂ)‖ = |hbar| := by simp
  rw [this] at h
  have : hbar ≤ |hbar| := le_abs_self _
  linarith

/-! ### A concrete instance: the Pauli observables on a qubit

This section checks that the hypotheses of `robertson_uncertainty` are satisfiable with a
*nonzero* commutator, so that the uncertainty bound above is not vacuous. -/

/-- The Pauli observable `σₓ` acting on a qubit. -/
