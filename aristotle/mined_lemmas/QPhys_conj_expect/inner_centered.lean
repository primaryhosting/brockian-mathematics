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

lemma inner_centered (A B : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) :
    ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, hA, hA, hψ, conj_expect A hA]
  simp only [expect]
  ring

/-- **The Robertson uncertainty relation.**  For any two symmetric operators `A`, `B`
(observables) on a complex inner product space and any normalized state `ψ`,
`ΔA · ΔB ≥ ‖⟪ψ, [A, B] ψ⟫‖ / 2`, where `[A, B] = A B - B A` is the commutator.

The proof is the classical one: expand the inner product of the centered vectors
`f = (A - ⟨A⟩)ψ`, `g = (B - ⟨B⟩)ψ`, note that `⟪f, g⟫ - ⟪g, f⟫ = ⟪ψ, [A,B] ψ⟫` equals
`2 i Im ⟪f, g⟫`, and apply the Cauchy–Schwarz inequality
`norm_inner_le_norm : ‖⟪f, g⟫‖ ≤ ‖f‖ * ‖g‖` from Mathlib. -/
