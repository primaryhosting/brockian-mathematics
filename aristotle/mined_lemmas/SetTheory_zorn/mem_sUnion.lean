import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem mem_sUnion {S : Set (Set α)} {a : α} : a ∈ sUnion S ↔ ∃ s, s ∈ S ∧ a ∈ s := Iff.rfl

