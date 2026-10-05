import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem IsChain.insert (hs : IsChain r s) {a : α}
    (ha : ∀ b, b ∈ s → a ≠ b → r a b ∨ r b a) : IsChain r (Set.insert a s) := by
  intro x hx y hy hxy
  rcases hx with hx | hx
  · subst hx
    rcases hy with hy | hy
    · exact absurd hy.symm hxy
    · exact ha y hy hxy
  · rcases hy with hy | hy
    · subst hy
      exact (ha x hx (fun h => hxy h.symm)).symm
    · exact hs hx hy hxy

/-! ### Hausdorff's maximality principle -/

/-- Predicate for whether a set is reachable from `∅` using `SuccChain` and `sUnion`. -/
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure r s → ChainClosure r (SuccChain r s)
  | union : ∀ {S : Set (Set α)}, (∀ s, s ∈ S → ChainClosure r s) → ChainClosure r (sUnion S)

/-- An explicit maximal chain: the union of all sets in `ChainClosure`. -/
