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
theorem halls_marriage {V W : Type*} [Fintype V] [Fintype W] (r : V → W → Prop)
    [DecidableRel r] :
    (∀ A : Finset V, #A ≤ #{w | ∃ v ∈ A, r v w}) ↔
      ∃ f : V → W, Function.Injective f ∧ ∀ v, r v (f v) :=
  Fintype.all_card_le_filter_rel_iff_exists_injective r

/-- The bipartite graph on `V ⊕ W` whose edges are given by the relation `r : V → W → Prop`. -/
def bipartiteGraph {V W : Type*} (r : V → W → Prop) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl v, .inr w => r v w
    | .inr w, .inl v => r v w
    | _, _ => False
  symm := by rintro (a | a) (b | b) h <;> exact h
  loopless := ⟨by rintro (a | a) h <;> exact h⟩

@[simp] lemma bipartiteGraph_adj_inl_inr {V W : Type*} (r : V → W → Prop) (v : V) (w : W) :
    (bipartiteGraph r).Adj (.inl v) (.inr w) ↔ r v w := Iff.rfl

@[simp] lemma bipartiteGraph_adj_inr_inl {V W : Type*} (r : V → W → Prop) (v : V) (w : W) :
    (bipartiteGraph r).Adj (.inr w) (.inl v) ↔ r v w := Iff.rfl

@[simp] lemma bipartiteGraph_adj_inl_inl {V W : Type*} (r : V → W → Prop) (v v' : V) :
    ¬ (bipartiteGraph r).Adj (.inl v) (.inl v') := id

@[simp] lemma bipartiteGraph_adj_inr_inr {V W : Type*} (r : V → W → Prop) (w w' : W) :
    ¬ (bipartiteGraph r).Adj (.inr w) (.inr w') := id

/-- From a perfect matching of the bipartite graph one extracts an injective map `V → W`
picking, for each `v`, its partner. -/
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
theorem halls_marriage_perfectMatching {V W : Type*} [Fintype V] [Fintype W]
    (hcard : Fintype.card V = Fintype.card W) (r : V → W → Prop) [DecidableRel r] :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔
      ∀ A : Finset V, #A ≤ #{w | ∃ v ∈ A, r v w} := by
  constructor
  · rintro ⟨M, hM⟩
    exact (halls_marriage r).mpr (exists_injective_of_isPerfectMatching r hM)
  · intro h
    obtain ⟨f, hf, hr⟩ := (halls_marriage r).mp h
    exact exists_isPerfectMatching_of_injective hcard r hf hr

end Math

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

