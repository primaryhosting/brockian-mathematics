/-
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

variable {α : Type*} [CompleteLattice α]

/-- The candidate least fixed point of `f`: the infimum of all pre-fixed points
(the points `x` with `f x ≤ x`). -/

theorem f_lfpCandidate_le {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro x hx
  exact le_trans (hf (lfpCandidate_le hx)) hx

/-- For monotone `f`, `lfpCandidate f` is itself a pre-fixed point, hence a fixed point. -/
