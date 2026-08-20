import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {α β : Type*}

/-- A simple graph on `α ⊕ β` is *bipartite* (with respect to the given splitting of its
vertex type) if every edge joins a vertex of `α` to a vertex of `β`. -/
def IsBipartiteSum (G : SimpleGraph (α ⊕ β)) : Prop :=
  ∀ x y : α ⊕ β, G.Adj x y → x.isLeft = !y.isLeft

/-- From a perfect matching of a bipartite graph, every left vertex is matched to a right
vertex. -/
theorem exists_right_of_perfectMatching {G : SimpleGraph (α ⊕ β)} (hbip : IsBipartiteSum G)
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (a : α) :
    ∃ b : β, M.Adj (Sum.inl a) (Sum.inr b) := by
  obtain ⟨w, hw, -⟩ := hM.1 (hM.2 (Sum.inl a))
  cases w with
  | inl a' =>
      exact absurd (hbip _ _ (M.adj_sub hw)) (by simp)
  | inr b => exact ⟨b, hw⟩

/-- From a perfect matching of a bipartite graph, every right vertex is matched to a left
vertex. -/
theorem exists_left_of_perfectMatching {G : SimpleGraph (α ⊕ β)} (hbip : IsBipartiteSum G)
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (b : β) :
    ∃ a : α, M.Adj (Sum.inl a) (Sum.inr b) := by
  obtain ⟨w, hw, -⟩ := hM.1 (hM.2 (Sum.inr b))
  cases w with
  | inl a => exact ⟨a, hw.symm⟩
  | inr b' =>
      exact absurd (hbip _ _ (M.adj_sub hw)) (by simp)

/-- A perfect matching of a bipartite graph yields an injection from the left side into the
right side along edges of the graph. -/
theorem exists_injective_left_of_perfectMatching {G : SimpleGraph (α ⊕ β)}
    (hbip : IsBipartiteSum G) {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, G.Adj (Sum.inl a) (Sum.inr (f a)) := by
  choose f hf using exists_right_of_perfectMatching hbip hM
  refine ⟨f, ?_, fun a => M.adj_sub (hf a)⟩
  intro a₁ a₂ h
  have := hM.1.eq_of_adj_right (hf a₁) (h ▸ hf a₂)
  simpa using this

/-- A perfect matching of a bipartite graph yields an injection from the right side into the
left side along edges of the graph. -/
theorem exists_injective_right_of_perfectMatching {G : SimpleGraph (α ⊕ β)}
    (hbip : IsBipartiteSum G) {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ g : β → α, Function.Injective g ∧ ∀ b, G.Adj (Sum.inl (g b)) (Sum.inr b) := by
  choose g hg using exists_left_of_perfectMatching hbip hM
  refine ⟨g, ?_, fun b => M.adj_sub (hg b)⟩
  intro b₁ b₂ h
  have h2 : M.Adj (Sum.inl (g b₁)) (Sum.inr b₂) := by rw [h]; exact hg b₂
  have := hM.1.eq_of_adj_left (hg b₁) h2
  simpa using this

/-- An equivalence `α ≃ β` all of whose graphs are edges gives a perfect matching. -/
theorem exists_perfectMatching_of_equiv {G : SimpleGraph (α ⊕ β)} (e : α ≃ β)
    (he : ∀ a, G.Adj (Sum.inl a) (Sum.inr (e a))) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  refine ⟨{ verts := Set.univ
            Adj := fun x y =>
              (∃ a, x = Sum.inl a ∧ y = Sum.inr (e a)) ∨ (∃ a, y = Sum.inl a ∧ x = Sum.inr (e a))
            adj_sub := ?_
            edge_vert := ?_
            symm := ?_ }, ?_, ?_⟩
  · rintro x y (⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact he a
    · exact (he a).symm
  · intro _ _ _; trivial
  · rintro x y (⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact Or.inr ⟨a, rfl, rfl⟩
    · exact Or.inl ⟨a, rfl, rfl⟩
  · rintro v -
    cases v with
    | inl a =>
        refine ⟨Sum.inr (e a), Or.inl ⟨a, rfl, rfl⟩, ?_⟩
        rintro y (⟨a', ha', rfl⟩ | ⟨a', rfl, ha'⟩)
        · simp only [Sum.inl.injEq] at ha'; subst ha'; rfl
        · exact absurd ha' (by simp)
    | inr b =>
        refine ⟨Sum.inl (e.symm b), Or.inr ⟨e.symm b, rfl, by simp⟩, ?_⟩
        rintro y (⟨a', ha', rfl⟩ | ⟨a', rfl, ha'⟩)
        · exact absurd ha' (by simp)
        · simp only [Sum.inr.injEq] at ha'
          subst ha'
          simp
  · intro v; trivial

/-- Two injections in opposite directions along the edges of a bipartite graph give a perfect
matching. -/
theorem exists_perfectMatching_of_injective [Fintype α] [Fintype β] {G : SimpleGraph (α ⊕ β)}
    (hf : ∃ f : α → β, Function.Injective f ∧ ∀ a, G.Adj (Sum.inl a) (Sum.inr (f a)))
    (hg : ∃ g : β → α, Function.Injective g ∧ ∀ b, G.Adj (Sum.inl (g b)) (Sum.inr b)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨f, hfinj, hfadj⟩ := hf
  obtain ⟨g, hginj, -⟩ := hg
  have hcard : Fintype.card α = Fintype.card β :=
    le_antisymm (Fintype.card_le_of_injective f hfinj) (Fintype.card_le_of_injective g hginj)
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩
  refine exists_perfectMatching_of_equiv (Equiv.ofBijective f hbij) ?_
  intro a
  simpa [Equiv.ofBijective] using hfadj a

/-- **Hall's Marriage Theorem** for bipartite graphs.

Let `G` be a bipartite graph on the (finite) vertex type `α ⊕ β`, meaning that every edge joins
a vertex on the left to a vertex on the right.  Then `G` has a perfect matching if and only if
Hall's condition holds on both sides: every set `s` of left vertices has at least `#s`
neighbours, and every set `t` of right vertices has at least `#t` neighbours. -/
theorem halls_marriage [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj]
    (hbip : IsBipartiteSum G) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ((∀ s : Finset α,
          s.card ≤ (Finset.univ.filter
            (fun b : β => ∃ a ∈ s, G.Adj (Sum.inl a) (Sum.inr b))).card) ∧
       (∀ t : Finset β,
          t.card ≤ (Finset.univ.filter
            (fun a : α => ∃ b ∈ t, G.Adj (Sum.inl a) (Sum.inr b))).card)) := by
  have hleft := Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (a : α) (b : β) => G.Adj (Sum.inl a) (Sum.inr b))
  have hright := Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (b : β) (a : α) => G.Adj (Sum.inl a) (Sum.inr b))
  rw [hleft, hright]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨exists_injective_left_of_perfectMatching hbip hM,
      exists_injective_right_of_perfectMatching hbip hM⟩
  · rintro ⟨hf, hg⟩
    exact exists_perfectMatching_of_injective hf hg

end Math

