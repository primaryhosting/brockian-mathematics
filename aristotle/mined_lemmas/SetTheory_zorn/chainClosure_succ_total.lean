import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

private theorem chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ ⊆ c₂) : c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ with
  | @succ c₃ hc₃ ih =>
    rcases chainClosure_succ_total_aux hc₁ (fun {c₄} hc₄ h₄ => ih hc₄ h₄) with h₁ | h₁
    · exact Or.inl (Subset.antisymm h₁ h)
    · rcases ih hc₁ h₁ with heq | h₂
      · exact Or.inr (subset_of_eq (congrArg (SuccChain r) heq.symm))
      · exact Or.inr (Subset.trans h₂ subset_succChain)
  | @union S hS ih =>
    by_cases hsub : sUnion S ⊆ c₁
    · exact Or.inl (Subset.antisymm hsub h)
    · refine Or.inr ?_
      have hex : ∃ c₃, c₃ ∈ S ∧ ¬ c₃ ⊆ c₁ := by
        apply Classical.byContradiction
        intro hcon
        exact hsub (sUnion_subset fun t ht =>
          Classical.byContradiction fun hnt => hcon ⟨t, ht, hnt⟩)
      obtain ⟨c₃, hc₃, h₁⟩ := hex
      apply Classical.byContradiction
      intro h₂
      rcases chainClosure_succ_total_aux hc₁ (fun {c₄} hc₄ h₄ => ih c₃ hc₃ hc₄ h₄) with hx | hx
      · exact h₁ (Subset.trans subset_succChain hx)
      · rcases ih c₃ hc₃ hc₁ hx with hy | hy
        · exact h₁ (subset_of_eq hy)
        · exact h₂ (Subset.trans hy (subset_sUnion_of_mem hc₃))

