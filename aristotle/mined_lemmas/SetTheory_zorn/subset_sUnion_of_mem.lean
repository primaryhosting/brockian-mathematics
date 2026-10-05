import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem subset_sUnion_of_mem {S : Set (Set α)} {s : Set α} (h : s ∈ S) : s ⊆ sUnion S :=
  fun _ ha => ⟨s, h, ha⟩

