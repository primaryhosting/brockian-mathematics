import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

def SuperChain (r : α → α → Prop) (s t : Set α) : Prop := IsChain r t ∧ s ⊆ t ∧ s ≠ t

/-- A chain `s` is maximal if no chain strictly contains it. -/
