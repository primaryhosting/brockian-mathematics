/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module doc-comment `/-! ... -/`, so the
-- header above is written as a plain block comment and repeated as a docstring below.)

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

/-- The expectation value `⟨A⟩_ψ` of an operator `A` in the state `ψ`.
For a symmetric (observable) operator and a normalized state this is the physical
expectation value; we take the real part so that it is a real number by construction. -/

lemma inner_centered (A B : H →ₗ[ℂ] H) (ψ : H) (a b : ℝ)
    (hψ : ‖ψ‖ = 1) (hA : ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ) :
    ⟪A ψ - (a : ℂ) • ψ, B ψ - (b : ℂ) • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - (b : ℂ) * ⟪ψ, A ψ⟫_ℂ - (a : ℂ) * ⟪ψ, B ψ⟫_ℂ
        + (a : ℂ) * (b : ℂ) := by
  have hnn : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hnn]
  rw [hA ψ (B ψ), hA ψ ψ]
  ring

/-- **Heisenberg uncertainty principle** (absolute-value form).
If `X` and `P` are symmetric operators on a complex inner product space satisfying the
canonical commutation relation `[X, P] ψ = i ℏ ψ` at a normalized state `ψ`, then
`Δx · Δp ≥ |ℏ| / 2`. -/
