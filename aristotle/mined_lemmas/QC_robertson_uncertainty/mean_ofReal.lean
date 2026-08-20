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

theorem mean_ofReal {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (ψ : E) :
    ((mean A ψ : ℝ) : ℂ) = ⟪ψ, A ψ⟫ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  rw [mean, ← Complex.conj_eq_iff_re, inner_conj_symm]
  simpa using (hs ψ ψ)

/-- The inner product of the two centred vectors `(A - ⟨A⟩)ψ` and `(B - ⟨B⟩)ψ`. -/
