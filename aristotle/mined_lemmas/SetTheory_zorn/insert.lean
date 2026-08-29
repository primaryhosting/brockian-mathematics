import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

protected def insert (a : α) (s : Set α) : Set α := fun b => b = a ∨ b ∈ s

