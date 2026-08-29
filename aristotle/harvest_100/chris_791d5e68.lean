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
theorem lfpCandidate_le {f : α → α} {x : α} (hx : f x ≤ x) : lfpCandidate f ≤ x :=
  sInf_le hx

/-- For monotone `f`, `f` maps `lfpCandidate f` below itself. -/
theorem f_lfpCandidate_le {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro x hx
  exact le_trans (hf (lfpCandidate_le hx)) hx

/-- For monotone `f`, `lfpCandidate f` is itself a pre-fixed point, hence a fixed point. -/
theorem lfpCandidate_isFixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) = lfpCandidate f := by
  have h1 : f (lfpCandidate f) ≤ lfpCandidate f := f_lfpCandidate_le hf
  have h2 : lfpCandidate f ≤ f (lfpCandidate f) :=
    lfpCandidate_le (hf h1)
  exact le_antisymm h1 h2

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b :=
  ⟨lfpCandidate f, lfpCandidate_isFixed hf, fun _ hb => lfpCandidate_le hb.le⟩

end CS

