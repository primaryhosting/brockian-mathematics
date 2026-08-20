import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command in a file
-- (a `/-! ... -/` module docstring is a command), so the required header comment
-- appears immediately after the single `import Mathlib` line.

open scoped ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => (inner ℂ x y : ℂ)

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`
(a real number when `A` is self-adjoint and `ψ` is a unit vector). -/

theorem inner_shift {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - ((mean A ψ : ℂ)) • ψ, B ψ - ((mean B ψ : ℂ)) • ψ⟫
      = ⟪ψ, (A * B) ψ⟫ - ((mean A ψ : ℂ) * (mean B ψ : ℂ)) := by
  have hsA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAB : ⟪A ψ, B ψ⟫ = ⟪ψ, (A * B) ψ⟫ := by
    simpa using (hsA ψ (B ψ))
  have hAψ : ⟪A ψ, ψ⟫ = ((mean A ψ : ℂ)) := by
    rw [mean_ofReal hA]
    simpa using (hsA ψ ψ)
  have hBψ : ⟪ψ, B ψ⟫ = ((mean B ψ : ℂ)) := (mean_ofReal hB ψ).symm
  have hnn : ⟪ψ, ψ⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hAB, hAψ, hBψ, hnn]
  ring

/-- For a self-adjoint `A` and a unit vector `ψ`, `(ΔA)² = ⟨A²⟩ - ⟨A⟩²`,
i.e. `Delta` is the square root of the usual quantum-mechanical variance. -/
