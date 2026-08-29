import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ hs => hs

