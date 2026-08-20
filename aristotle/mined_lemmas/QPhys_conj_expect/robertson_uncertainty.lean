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

theorem robertson_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    spread A ψ * spread B ψ ≥ ‖⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ‖ / 2 := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  set f := A ψ - expect A ψ • ψ with hf
  set g := B ψ - expect B ψ • ψ with hg
  -- the commutator identity transported to the centered vectors
  have hkey : ⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ = ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ := by
    rw [hf, hg, inner_centered A B hA ψ hψψ, inner_centered B A hB ψ hψψ, inner_sub_right]
    ring
  -- the commutator expectation is `2 i Im ⟪f, g⟫`
  have hconj : ⟪g, f⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ := (inner_conj_symm g f).symm
  have hnorm : ‖⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ‖ = 2 * |(⟪f, g⟫_ℂ).im| := by
    rw [← hkey, hconj, Complex.sub_conj]
    simp
  rw [hnorm]
  have hcs : ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g
  have him : |(⟪f, g⟫_ℂ).im| ≤ ‖⟪f, g⟫_ℂ‖ := Complex.abs_im_le_norm _
  have : ‖f‖ * ‖g‖ = spread A ψ * spread B ψ := rfl
  linarith [him.trans hcs]

/-- **Heisenberg's uncertainty principle.**  If `A` and `B` are symmetric operators
(observables, e.g. position and momentum) on a complex inner product space satisfying the
canonical commutation relation `[A, B] = i ℏ`, then for every normalized state `ψ`
the product of the uncertainties satisfies `ΔA · ΔB ≥ ℏ / 2`. -/
