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

theorem lfpCandidate_le_apply {f : α → α} (hf : Monotone f) :
    lfpCandidate f ≤ f (lfpCandidate f) :=
  sInf_le (hf (lfpCandidate_prefixed hf))

/-- `lfpCandidate f` is a fixed point of `f`. -/
