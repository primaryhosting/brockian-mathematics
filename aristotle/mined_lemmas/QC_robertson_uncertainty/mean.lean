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

noncomputable def mean (A : E →L[ℂ] E) (ψ : E) : ℝ := Complex.re ⟪ψ, A ψ⟫

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
