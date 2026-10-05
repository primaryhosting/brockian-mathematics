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

@[simp] lemma commutator_apply (A B : E →ₗ[ℂ] E) (x : E) :
    commutator A B x = A (B x) - B (A x) := rfl

/-- The expectation value of an observable is real. -/
