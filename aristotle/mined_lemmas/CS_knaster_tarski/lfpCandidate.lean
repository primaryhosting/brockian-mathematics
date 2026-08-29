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

def lfpCandidate (f : α → α) : α := sInf {x | f x ≤ x}

/-- `lfpCandidate f` is a lower bound of the set of pre-fixed points. -/
