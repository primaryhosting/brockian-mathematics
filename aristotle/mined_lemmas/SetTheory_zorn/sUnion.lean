import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

def sUnion (S : Set (Set α)) : Set α := fun a => ∃ s, s ∈ S ∧ a ∈ s

