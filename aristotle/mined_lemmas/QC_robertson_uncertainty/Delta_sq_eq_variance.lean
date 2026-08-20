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

theorem Delta_sq_eq_variance {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {ψ : E} (hψ : ‖ψ‖ = 1) :
    (Delta A ψ) ^ 2 = Complex.re ⟪ψ, (A * A) ψ⟫ - (mean A ψ) ^ 2 := by
  have h := inner_shift hA hA hψ
  have h2 : Complex.re ⟪A ψ - ((mean A ψ : ℂ)) • ψ, A ψ - ((mean A ψ : ℂ)) • ψ⟫
      = (Delta A ψ) ^ 2 := by
    simpa [Delta] using inner_self_eq_norm_sq (𝕜 := ℂ) (A ψ - ((mean A ψ : ℂ)) • ψ)
  rw [← h2, h]
  simp [sq]

/-- For a complex number `z`, `‖z - conj z‖ = 2 |Im z| ≤ 2 ‖z‖`. -/
