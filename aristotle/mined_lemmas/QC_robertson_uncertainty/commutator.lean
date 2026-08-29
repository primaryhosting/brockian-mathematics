/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An *observable* is a symmetric (self-adjoint) linear operator on a complex
inner product space. -/

noncomputable def commutator (A B : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := A ∘ₗ B - B ∘ₗ A

