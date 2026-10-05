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

lemma conj_expect_of_observable {A : E →ₗ[ℂ] E} (hA : IsObservable A) (ψ : E) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm, hA]

/-- The inner product of the two deviation vectors, expressed via `⟪ψ, A (B ψ)⟫`. -/
