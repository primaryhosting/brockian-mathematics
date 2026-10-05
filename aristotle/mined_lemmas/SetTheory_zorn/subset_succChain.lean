import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem subset_succChain : s ⊆ SuccChain r s := by
  classical
  by_cases h : ∃ t, IsChain r s ∧ SuperChain r s t
  · exact (succChain_spec h).2.1
  · rw [SuccChain, dif_neg h]; exact Subset.rfl

