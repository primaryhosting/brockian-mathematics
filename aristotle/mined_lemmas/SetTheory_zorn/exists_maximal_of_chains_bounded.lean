import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem exists_maximal_of_chains_bounded
    (h : ∀ c : Set α, IsChain r c → ∃ ub, ∀ a, a ∈ c → r a ub)
    (trans : ∀ {a b c : α}, r a b → r b c → r a c) : ∃ m, ∀ a, r m a → r a m := by
  obtain ⟨ub, hub⟩ := h (maxChain r) maxChain_spec.1
  refine ⟨ub, fun a ha => ?_⟩
  have hchain : IsChain r (Set.insert a (maxChain r)) :=
    maxChain_spec.1.insert fun b hb _ => Or.inr (trans (hub b hb) ha)
  have heq : maxChain r = Set.insert a (maxChain r) :=
    maxChain_spec.2 hchain (subset_insert _ _)
  exact hub a (heq ▸ Set.mem_insert a (maxChain r))

/-- **Zorn's lemma**: in a preorder in which every chain has an upper bound, there is a maximal
element `m`, i.e. every `a` with `m ≤ a` also satisfies `a ≤ m`. -/
