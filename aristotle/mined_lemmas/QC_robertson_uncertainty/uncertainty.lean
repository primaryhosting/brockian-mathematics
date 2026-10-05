/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟨ψ|A|ψ⟩` of an observable `A` in the state `ψ`. -/

noncomputable def uncertainty (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = AB - BA`. -/
