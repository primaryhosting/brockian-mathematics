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

lemma exists_injective_of_isPerfectMatching {V W : Type*} (r : V → W → Prop)
    {M : (bipartiteGraph r).Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : V → W, Function.Injective f ∧ ∀ v, r v (f v) := by
  classical
  obtain ⟨hmatch, hspan⟩ := hM
  have key : ∀ v : V, ∃ w : W, M.Adj (Sum.inl v) (Sum.inr w) := by
    intro v
    obtain ⟨y, hy, -⟩ := hmatch (hspan (Sum.inl v))
    have hGy := M.adj_sub hy
    cases y with
    | inl v' => exact absurd hGy (bipartiteGraph_adj_inl_inl r v v')
    | inr w => exact ⟨w, hy⟩
  choose f hf using key
  refine ⟨f, ?_, fun v => M.adj_sub (hf v)⟩
  intro v₁ v₂ hv
  obtain ⟨y, -, huniq⟩ := hmatch (hspan (Sum.inr (f v₁)))
  have h₁ : Sum.inl v₁ = y := huniq _ (M.symm (hf v₁))
  have h₂ : Sum.inl v₂ = y := huniq _ (M.symm (hv ▸ hf v₂))
  exact Sum.inl_injective (h₁.trans h₂.symm)

/-- From an injective map `V → W` respecting `r`, when `|V| = |W|`, one builds a perfect
matching of the bipartite graph. -/
