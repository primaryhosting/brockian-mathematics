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

theorem lfpCandidate_le {f : α → α} {x : α} (hx : f x ≤ x) : lfpCandidate f ≤ x :=
  sInf_le hx

/-- For monotone `f`, `f` maps `lfpCandidate f` below itself. -/
