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

/-- The candidate least fixed point of `f`: the infimum of all pre-fixed points. -/
noncomputable def lfpCandidate (f : α → α) : α := sInf {x | f x ≤ x}

/-- `f (lfpCandidate f) ≤ lfpCandidate f` for monotone `f`. -/
theorem lfpCandidate_prefixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) ≤ lfpCandidate f := by
  refine le_sInf ?_
  intro x hx
  exact (hf (sInf_le hx)).trans hx

/-- `lfpCandidate f ≤ f (lfpCandidate f)` for monotone `f`. -/
theorem lfpCandidate_le_apply {f : α → α} (hf : Monotone f) :
    lfpCandidate f ≤ f (lfpCandidate f) :=
  sInf_le (hf (lfpCandidate_prefixed hf))

/-- `lfpCandidate f` is a fixed point of `f`. -/
theorem lfpCandidate_fixed {f : α → α} (hf : Monotone f) :
    f (lfpCandidate f) = lfpCandidate f :=
  le_antisymm (lfpCandidate_prefixed hf) (lfpCandidate_le_apply hf)

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] {f : α → α} (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b := by
  refine ⟨lfpCandidate f, lfpCandidate_fixed hf, ?_⟩
  intro b hb
  exact sInf_le hb.le

end CS

