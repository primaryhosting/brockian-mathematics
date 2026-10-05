import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The largest cardinality of a chain contained in the finite set `t`. -/

lemma longestChainCard_le_card_of_cover {F : Finset (Finset α)} (hF : IsAntichainCover F) :
    longestChainCard α ≤ F.card := by
  obtain ⟨C, -, hchain, hcard⟩ := exists_chain_card_eq_chainSup (Finset.univ : Finset α)
  have hpick : ∀ x : α, ∃ s, s ∈ F ∧ x ∈ s := fun x => hF.2 x
  choose g hgF hgmem using hpick
  have hinj : Set.InjOn g (C : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have hax := hF.1 (g x) (hgF x)
    have hxs : x ∈ (g x : Set α) := hgmem x
    have hys : y ∈ (g x : Set α) := by rw [hxy]; exact hgmem y
    rcases hchain hx hy hne with h | h
    · exact hax hxs hys hne h
    · exact hax hys hxs (Ne.symm hne) h
  have := Finset.card_le_card_of_injOn g (fun x _ => hgF x) hinj
  rw [longestChainCard, ← hcard]
  exact this

/-- The levels of the height function form an antichain cover with at most
`longestChainCard α` members. -/
