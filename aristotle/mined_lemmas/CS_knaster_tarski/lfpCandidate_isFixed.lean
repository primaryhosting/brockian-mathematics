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

theorem lfpCandidate_isFixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) = lfpCandidate f := by
  have h1 : f (lfpCandidate f) ≤ lfpCandidate f := f_lfpCandidate_le hf
  have h2 : lfpCandidate f ≤ f (lfpCandidate f) :=
    lfpCandidate_le (hf h1)
  exact le_antisymm h1 h2

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
