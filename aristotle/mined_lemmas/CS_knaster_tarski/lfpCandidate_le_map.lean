/-
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

section

variable {α : Type*} [CompleteLattice α] (f : α → α)

/-- The candidate least fixed point: the infimum of all pre-fixed points of `f`. -/

theorem lfpCandidate_le_map (hf : Monotone f) : lfpCandidate f ≤ f (lfpCandidate f) :=
  lfpCandidate_le (hf (map_lfpCandidate_le hf))

/-- The candidate is a fixed point. -/
