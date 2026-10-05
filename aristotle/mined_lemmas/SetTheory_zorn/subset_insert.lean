import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem subset_insert (a : α) (s : Set α) : s ⊆ Set.insert a s := fun _ ha => Or.inr ha

end Set

open Set

/-! ### Chains -/

/-- A chain is a set whose elements are pairwise comparable for `r`. -/
