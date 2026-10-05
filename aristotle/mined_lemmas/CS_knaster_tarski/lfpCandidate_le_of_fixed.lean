/-
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS


variable {α : Type*} [CompleteLattice α] {f : α → α}

/-- The candidate least fixed point: the infimum of all pre-fixed points of `f`. -/

theorem lfpCandidate_le_of_fixed {a : α} (ha : f a = a) : lfpCandidate f ≤ a :=
  sInf_le (le_of_eq ha)

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
