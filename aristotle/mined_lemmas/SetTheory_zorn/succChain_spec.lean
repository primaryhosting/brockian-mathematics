import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem succChain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  classical
  have hs : IsChain r s ∧ SuperChain r s (Classical.choose h) := Classical.choose_spec h
  rw [SuccChain, dif_pos h]
  exact hs.2

