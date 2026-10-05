import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem subset_of_eq {s t : Set α} (h : s = t) : s ⊆ t := h ▸ Subset.rfl

/-- The union of a family of sets. -/
