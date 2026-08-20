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

theorem lfpCandidate_fixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) = lfpCandidate f :=
  le_antisymm (lfpCandidate_prefixed hf) (lfpCandidate_le_apply hf)

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
