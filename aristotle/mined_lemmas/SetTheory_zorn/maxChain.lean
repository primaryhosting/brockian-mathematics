import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

noncomputable def maxChain (r : α → α → Prop) : Set α := sUnion (fun s => ChainClosure r s)

