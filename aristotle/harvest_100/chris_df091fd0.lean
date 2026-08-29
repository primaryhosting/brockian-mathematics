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

variable {α : Type*} [CompleteLattice α]

/-- The candidate least fixed point of `f`: the infimum of all pre-fixed points
(points `a` with `f a ≤ a`). -/
def lfpCandidate (f : α → α) : α := sInf {a | f a ≤ a}

/-- `f (lfpCandidate f) ≤ lfpCandidate f` for monotone `f`. -/
theorem lfpCandidate_prefixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro a ha
  exact le_trans (hf (sInf_le ha)) ha

/-- `lfpCandidate f ≤ f (lfpCandidate f)` for monotone `f`. -/
theorem lfpCandidate_le_apply {f : α → α} (hf : Monotone f) :
    lfpCandidate f ≤ f (lfpCandidate f) :=
  sInf_le (hf (lfpCandidate_prefixed hf))

/-- `lfpCandidate f` is a fixed point of a monotone `f`. -/
theorem lfpCandidate_fixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) = lfpCandidate f :=
  le_antisymm (lfpCandidate_prefixed hf) (lfpCandidate_le_apply hf)

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
theorem knaster_tarski (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b := by
  refine ⟨lfpCandidate f, lfpCandidate_fixed hf, ?_⟩
  intro b hb
  exact sInf_le hb.le

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

