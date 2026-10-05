import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ s, s ∈ S → s ⊆ t) : sUnion S ⊆ t :=
  fun _ ha => match ha with | ⟨s, hs, has⟩ => h s hs has

/-- Insert an element into a set. -/
