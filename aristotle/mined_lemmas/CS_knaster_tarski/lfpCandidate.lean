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

noncomputable def lfpCandidate (f : α → α) : α := sInf {x | f x ≤ x}

/-- `f (lfpCandidate f) ≤ lfpCandidate f` for monotone `f`. -/
