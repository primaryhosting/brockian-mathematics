import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma frag_key {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H)
    {Ŝ : Finset X} (hŜ : Ŝ ∈ H) (hsub : Ŝ ⊆ W ∪ frag H W S) :
    frag H W S ⊆ Ŝ := by
  set T := frag H W S with hT
  -- `Ŝ \ W ⊆ T`
  have h1 : Ŝ \ W ⊆ T := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy
    rcases Finset.mem_union.mp (hsub hy.1) with h | h
    · exact absurd h hy.2
    · exact h
  -- `Ŝ` is a candidate, so `|T| ≤ |Ŝ \ W|`
  have h2 : Ŝ \ W ∈ cand H W S := by
    have hŜsub : Ŝ ⊆ W ∪ S := by
      intro y hy
      rcases Finset.mem_union.mp (hsub hy) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (frag_subset hS h)
    simp only [cand, Finset.mem_image, Finset.mem_filter]
    exact ⟨Ŝ, ⟨hŜ, hŜsub⟩, rfl⟩
  have h3 : T.card ≤ (Ŝ \ W).card := frag_min hS _ h2
  have h4 : Ŝ \ W = T := Finset.eq_of_subset_of_card_le h1 h3
  calc T = Ŝ \ W := h4.symm
    _ ⊆ Ŝ := Finset.sdiff_subset

/-- Edges whose minimum fragment is large. -/
