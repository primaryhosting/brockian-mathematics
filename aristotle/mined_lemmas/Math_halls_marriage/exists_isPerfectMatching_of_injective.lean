import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Function

namespace Math

/-- **Hall's Marriage Theorem** for a bipartite graph.

The bipartite graph is given by its adjacency relation `r : V → W → Prop` between the two
(finite) sides `V` and `W`.  A *matching saturating `V`* is an injective function `f : V → W`
with `v` adjacent to `f v` for every `v : V`.

Such a matching exists if and only if *Hall's condition* holds: every set `A` of vertices of
`V` has at least `#A` neighbours in `W`.

This is Mathlib's `Fintype.all_card_le_filter_rel_iff_exists_injective`. -/

lemma exists_isPerfectMatching_of_injective {V W : Type*} [Fintype V] [Fintype W]
    (hcard : Fintype.card V = Fintype.card W) (r : V → W → Prop)
    {f : V → W} (hf : Function.Injective f) (hr : ∀ v, r v (f v)) :
    ∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching := by
  classical
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  refine ⟨{ verts := Set.univ
            Adj := fun x y => (∃ v, x = Sum.inl v ∧ y = Sum.inr (f v)) ∨
                              (∃ v, y = Sum.inl v ∧ x = Sum.inr (f v))
            adj_sub := ?_
            edge_vert := ?_
            symm := ?_ }, ?_, fun _ => Set.mem_univ _⟩
  · rintro x y (⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩) <;> exact hr v
  · intro x y _
    exact Set.mem_univ _
  · rintro x y (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (v | w) -
    · refine ⟨Sum.inr (f v), Or.inl ⟨v, rfl, rfl⟩, ?_⟩
      rintro y (⟨v', hv', rfl⟩ | ⟨v', rfl, hv'⟩)
      · rw [Sum.inl_injective hv']
      · exact absurd hv' (by simp)
    · obtain ⟨v, rfl⟩ := hbij.surjective w
      refine ⟨Sum.inl v, Or.inr ⟨v, rfl, rfl⟩, ?_⟩
      rintro y (⟨v', hv', rfl⟩ | ⟨v', rfl, hv'⟩)
      · exact absurd hv' (by simp)
      · rw [hf (Sum.inr_injective hv').symm]

/-- **Hall's Marriage Theorem**, graph-theoretic form: a bipartite graph with parts of equal
(finite) size has a perfect matching if and only if Hall's condition holds, i.e. every set `A`
of vertices in one part has at least `#A` neighbours in the other part. -/
