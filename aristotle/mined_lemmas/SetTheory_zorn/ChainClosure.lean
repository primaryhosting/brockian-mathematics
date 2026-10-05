import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ ih => exact ih.succ
  | @union S hS ih =>
    intro x hx y hy hxy
    obtain ⟨t₁, ht₁, hx₁⟩ := hx
    obtain ⟨t₂, ht₂, hy₂⟩ := hy
    rcases ChainClosure.total (hS _ ht₁) (hS _ ht₂) with ht | ht
    · exact ih t₂ ht₂ (ht hx₁) hy₂ hxy
    · exact ih t₁ ht₁ hx₁ (ht hy₂) hxy

/-- **Hausdorff's maximality principle**: `maxChain r` is a maximal chain. -/
