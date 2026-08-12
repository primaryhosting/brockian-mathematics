import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset Function

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` determined by a relation `r : V → W → Prop`:
the only edges join a vertex `v` of the left part to a vertex `w` of the right part,
and such an edge is present exactly when `r v w` holds. -/
def bipartiteGraph (r : V → W → Prop) : SimpleGraph (V ⊕ W) where
  Adj a b :=
    (∃ v w, a = Sum.inl v ∧ b = Sum.inr w ∧ r v w) ∨
      (∃ v w, b = Sum.inl v ∧ a = Sum.inr w ∧ r v w)
  symm := by
    rintro a b (h | h)
    · exact Or.inr h
    · exact Or.inl h
  loopless := ⟨by rintro a (⟨v, w, rfl, h, -⟩ | ⟨v, w, h, h', -⟩) <;> simp_all⟩

@[simp]
lemma bipartiteGraph_adj_inl_inr (r : V → W → Prop) (v : V) (w : W) :
    (bipartiteGraph r).Adj (Sum.inl v) (Sum.inr w) ↔ r v w := by
  constructor
  · rintro (⟨v', w', h1, h2, h3⟩ | ⟨v', w', h1, h2, h3⟩) <;> simp_all
  · intro h; exact Or.inl ⟨v, w, rfl, rfl, h⟩

@[simp]
lemma bipartiteGraph_adj_inr_inl (r : V → W → Prop) (v : V) (w : W) :
    (bipartiteGraph r).Adj (Sum.inr w) (Sum.inl v) ↔ r v w := by
  rw [SimpleGraph.adj_comm, bipartiteGraph_adj_inl_inr]

@[simp]
lemma bipartiteGraph_not_adj_inl_inl (r : V → W → Prop) (v v' : V) :
    ¬ (bipartiteGraph r).Adj (Sum.inl v) (Sum.inl v') := by
  rintro (⟨a, b, h1, h2, -⟩ | ⟨a, b, h1, h2, -⟩) <;> simp_all

@[simp]
lemma bipartiteGraph_not_adj_inr_inr (r : V → W → Prop) (w w' : W) :
    ¬ (bipartiteGraph r).Adj (Sum.inr w) (Sum.inr w') := by
  rintro (⟨a, b, h1, h2, -⟩ | ⟨a, b, h1, h2, -⟩) <;> simp_all

/-- The subgraph of `bipartiteGraph r` given by the edges `v -- e v` for an equivalence `e`
compatible with `r`. -/
def matchingSubgraph (r : V → W → Prop) (e : V ≃ W) (he : ∀ v, r v (e v)) :
    (bipartiteGraph r).Subgraph where
  verts := Set.univ
  Adj a b := (∃ v, a = Sum.inl v ∧ b = Sum.inr (e v)) ∨ (∃ v, b = Sum.inl v ∧ a = Sum.inr (e v))
  adj_sub := by
    rintro a b (⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩)
    · simpa using he v
    · simpa using he v
  edge_vert := by intro a b _; trivial
  symm := by
    rintro a b (h | h)
    · exact Or.inr h
    · exact Or.inl h

lemma matchingSubgraph_isPerfectMatching (r : V → W → Prop) (e : V ≃ W) (he : ∀ v, r v (e v)) :
    (matchingSubgraph r e he).IsPerfectMatching := by
  constructor
  · rintro (v | w) -
    · refine ⟨Sum.inr (e v), Or.inl ⟨v, rfl, rfl⟩, ?_⟩
      rintro (v' | w') (⟨u, h1, h2⟩ | ⟨u, h1, h2⟩) <;> simp_all
    · refine ⟨Sum.inl (e.symm w), Or.inr ⟨e.symm w, rfl, by simp⟩, ?_⟩
      rintro (v' | w') (⟨u, h1, h2⟩ | ⟨u, h1, h2⟩) <;> simp_all
  · intro v; trivial

/-- From a perfect matching of the bipartite graph of `r` one extracts an equivalence
between the two sides which is compatible with `r`. -/
lemma exists_equiv_of_isPerfectMatching {r : V → W → Prop} {M : (bipartiteGraph r).Subgraph}
    (hM : M.IsPerfectMatching) : ∃ e : V ≃ W, ∀ v, r v (e v) := by
  have key : ∀ v : V, ∃! w : W, M.Adj (Sum.inl v) (Sum.inr w) := by
    intro v
    obtain ⟨x, hx, hu⟩ := hM.1 (hM.2 (Sum.inl v))
    cases x with
    | inl v' => exact absurd (M.adj_sub hx) (by simp)
    | inr w =>
      refine ⟨w, hx, ?_⟩
      intro w' hw'
      have := hu (Sum.inr w') hw'
      simpa using this
  have key2 : ∀ w : W, ∃! v : V, M.Adj (Sum.inr w) (Sum.inl v) := by
    intro w
    obtain ⟨x, hx, hu⟩ := hM.1 (hM.2 (Sum.inr w))
    cases x with
    | inr w' => exact absurd (M.adj_sub hx) (by simp)
    | inl v =>
      refine ⟨v, hx, ?_⟩
      intro v' hv'
      have := hu (Sum.inl v') hv'
      simpa using this
  classical
  refine ⟨⟨fun v => (key v).choose, fun w => (key2 w).choose, ?_, ?_⟩, ?_⟩
  · intro v
    have h1 : M.Adj (Sum.inl v) (Sum.inr ((key v).choose)) := (key v).choose_spec.1
    exact ((key2 ((key v).choose)).choose_spec.2 v h1.symm).symm
  · intro w
    have h1 : M.Adj (Sum.inr w) (Sum.inl ((key2 w).choose)) := (key2 w).choose_spec.1
    exact ((key ((key2 w).choose)).choose_spec.2 w h1.symm).symm
  · intro v
    have h1 : M.Adj (Sum.inl v) (Sum.inr ((key v).choose)) := (key v).choose_spec.1
    simpa using M.adj_sub h1

/-- The bipartite graph of `r` has a perfect matching iff there is an equivalence between the
two sides compatible with `r`. -/
lemma exists_isPerfectMatching_iff_exists_equiv (r : V → W → Prop) :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔ ∃ e : V ≃ W, ∀ v, r v (e v) := by
  constructor
  · rintro ⟨M, hM⟩
    exact exists_equiv_of_isPerfectMatching hM
  · rintro ⟨e, he⟩
    exact ⟨matchingSubgraph r e he, matchingSubgraph_isPerfectMatching r e he⟩

/-- **Hall's condition** for a bipartite graph given by `r : V → W → Prop`: every finite set of
vertices on either side has at least as many neighbours as it has elements. -/
def HallCondition [Fintype V] [Fintype W] (r : V → W → Prop) : Prop :=
  (∀ A : Finset V, #A ≤ #{b : W | ∃ a ∈ A, r a b}) ∧
    (∀ B : Finset W, #B ≤ #{a : V | ∃ b ∈ B, r a b})

lemma exists_equiv_iff_hallCondition [Fintype V] [Fintype W] (r : V → W → Prop) :
    (∃ e : V ≃ W, ∀ v, r v (e v)) ↔ HallCondition r := by
  classical
  constructor
  · rintro ⟨e, he⟩
    constructor
    · intro A
      refine le_trans (le_of_eq (Finset.card_image_of_injective A e.injective).symm) ?_
      refine Finset.card_le_card ?_
      intro b hb
      simp only [Finset.mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, he a⟩
    · intro B
      refine le_trans (le_of_eq (Finset.card_image_of_injective B e.symm.injective).symm) ?_
      refine Finset.card_le_card ?_
      intro a ha
      simp only [Finset.mem_image] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hb, ?_⟩
      have := he (e.symm b)
      simpa using this
  · rintro ⟨h1, h2⟩
    obtain ⟨f, hf, hfr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).1 (by
        intro A; simpa using h1 A)
    obtain ⟨g, hg, hgr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective (fun (b : W) (a : V) => r a b)).1 (by
        intro B; simpa using h2 B)
    have hcard : Fintype.card V = Fintype.card W :=
      le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    exact ⟨Equiv.ofBijective f hbij, fun v => hfr v⟩

/-- **Hall's marriage theorem.** The bipartite graph associated to a relation `r : V → W → Prop`
between two finite vertex sets has a perfect matching if and only if Hall's condition holds:
every set of vertices on either side has at least as many neighbours as elements. -/
theorem halls_marriage [Fintype V] [Fintype W] (r : V → W → Prop) :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔ HallCondition r := by
  rw [exists_isPerfectMatching_iff_exists_equiv, exists_equiv_iff_hallCondition]

end Math

