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
noncomputable def lfpCandidate (f : α → α) : α := sInf {x | f x ≤ x}

/-- `f` maps the candidate below itself. -/
theorem lfpCandidate_prefixed (hf : Monotone f) : f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro x hx
  exact le_trans (hf (sInf_le hx)) hx

/-- The candidate is in fact a fixed point. -/
theorem lfpCandidate_fixed (hf : Monotone f) : f (lfpCandidate f) = lfpCandidate f := by
  refine le_antisymm (lfpCandidate_prefixed hf) ?_
  exact sInf_le (hf (lfpCandidate_prefixed hf))

/-- The candidate is below every fixed point. -/
theorem lfpCandidate_le_of_fixed {a : α} (ha : f a = a) : lfpCandidate f ≤ a :=
  sInf_le (le_of_eq ha)

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
theorem knaster_tarski (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b :=
  ⟨lfpCandidate f, lfpCandidate_fixed hf, fun _ hb => lfpCandidate_le_of_fixed hb⟩

end CS

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

