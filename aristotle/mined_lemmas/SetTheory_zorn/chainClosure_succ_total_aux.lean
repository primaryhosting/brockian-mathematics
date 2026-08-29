import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

private theorem chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : ∀ {c₃}, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) :
    SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    rcases ih with ih | ih
    · exact Or.inl (Subset.trans ih subset_succChain)
    · rcases h hc₃ ih with heq | hsub
      · exact Or.inl (subset_of_eq (congrArg (SuccChain r) heq))
      · exact Or.inr hsub
  | @union S _ ih =>
    by_cases hn : SuccChain r c₂ ⊆ sUnion S
    · exact Or.inl hn
    · refine Or.inr (sUnion_subset fun a ha => ?_)
      rcases ih a ha with h' | h'
      · exact absurd (Subset.trans h' (subset_sUnion_of_mem ha)) hn
      · exact h'

