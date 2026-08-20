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

noncomputable def centered (A : E →ₗ[ℂ] E) (ψ : E) : E →ₗ[ℂ] E :=
  A - (expect A ψ) • LinearMap.id

/-- The variance of the observable `A` in the state `ψ`:
the real part of `⟪ψ, (A - ⟨A⟩)² ψ⟫`. -/
