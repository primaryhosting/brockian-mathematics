import Mathlib

/-!
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

variable {α : Type*} [CompleteLattice α]

/-- The candidate least fixed point of `f`: the infimum of all pre-fixed points. -/

theorem lfpCandidate_prefixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro x hx
  exact (hf (sInf_le hx)).trans hx

/-- `lfpCandidate f ≤ f (lfpCandidate f)` for monotone `f`. -/
