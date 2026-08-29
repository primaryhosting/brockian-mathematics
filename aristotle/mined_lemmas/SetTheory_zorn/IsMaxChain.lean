import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

def IsMaxChain (r : α → α → Prop) (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

open Classical in
/-- If the chain `s` admits a strictly larger chain, then `SuccChain r s` is one such chain;
otherwise `SuccChain r s = s`. -/
