import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a module,
so the mandated header comment is placed immediately after the single `import Mathlib` line.
-/

namespace QC

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

lemma Delta_eq_norm {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    Delta A ψ = ‖centered A ψ ψ‖ := by
  rw [Delta, variance_eq_norm_sq hA ψ, Real.sqrt_sq (norm_nonneg _)]

/-- Centering does not change the commutator. -/
