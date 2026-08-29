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
def lfpCandidate : α := sInf {x : α | f x ≤ x}

variable {f}

/-- The candidate is a lower bound of the set of pre-fixed points. -/
theorem lfpCandidate_le {x : α} (hx : f x ≤ x) : lfpCandidate f ≤ x :=
  sInf_le hx

/-- `f` maps the candidate below itself. -/
theorem map_lfpCandidate_le (hf : Monotone f) : f (lfpCandidate f) ≤ lfpCandidate f :=
  le_sInf fun _ hx => le_trans (hf (lfpCandidate_le hx)) hx

/-- The candidate is below its own image. -/
theorem lfpCandidate_le_map (hf : Monotone f) : lfpCandidate f ≤ f (lfpCandidate f) :=
  lfpCandidate_le (hf (map_lfpCandidate_le hf))

/-- The candidate is a fixed point. -/
theorem lfpCandidate_isFixed (hf : Monotone f) : f (lfpCandidate f) = lfpCandidate f :=
  le_antisymm (map_lfpCandidate_le hf) (lfpCandidate_le_map hf)

end

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b :=
  ⟨lfpCandidate f, lfpCandidate_isFixed hf, fun _ hb => lfpCandidate_le hb.le⟩

end CS

