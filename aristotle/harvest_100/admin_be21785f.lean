import Mathlib

/-!
# Hall's marriage theorem

A bipartite graph has a matching saturating one side iff Hall's condition holds,
and (when the two sides have the same size) a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
  (r : L → R → Prop) [∀ a, DecidablePred (r a)]

/-- The set of neighbours of a left vertex `a` in the bipartite graph given by `r`. -/
def neighbors (a : L) : Finset R := Finset.univ.filter (fun b => r a b)

omit [Fintype L] [DecidableEq R] in
@[simp] lemma mem_neighbors {a : L} {b : R} : b ∈ neighbors r a ↔ r a b := by
  simp [neighbors]

/-- Hall's condition: every set of left vertices has at least as many neighbours. -/
def HallCondition : Prop :=
  ∀ s : Finset L, s.card ≤ (s.biUnion (neighbors r)).card

/-- There is a matching saturating the left side: an injective choice of a neighbour
for every left vertex. -/
def HasLeftMatching : Prop :=
  ∃ f : L → R, Function.Injective f ∧ ∀ a, r a (f a)

omit [Fintype L] in
/-- **Hall's marriage theorem**: the bipartite graph given by `r` has a matching
saturating the left side iff Hall's condition holds. -/
theorem halls_marriage : HasLeftMatching r ↔ HallCondition r := by
  rw [HasLeftMatching, HallCondition]
  constructor
  · rintro ⟨f, hf, hfa⟩
    exact (Finset.all_card_le_biUnion_card_iff_exists_injective (neighbors r)).2
      ⟨f, hf, fun a => (mem_neighbors r).2 (hfa a)⟩
  · intro h
    obtain ⟨f, hf, hfa⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective (neighbors r)).1 h
    exact ⟨f, hf, fun a => (mem_neighbors r).1 (hfa a)⟩

/-- The bipartite graph on `L ⊕ R` whose edges are the pairs related by `r`. -/
def bipartiteGraph : SimpleGraph (L ⊕ R) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr b => r a b
    | Sum.inr b, Sum.inl a => r a b
    | _, _ => False
  symm := by rintro (a | b) (c | d) h <;> exact h
  loopless := by constructor; rintro (a | b) h <;> simp at h

/-- **Hall's marriage theorem, graph form**: if the two sides have the same size, the
bipartite graph given by `r` has a perfect matching iff Hall's condition holds. -/
theorem bipartiteGraph_exists_isPerfectMatching_iff
    (hcard : Fintype.card L = Fintype.card R) :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔ HallCondition r := by
  rw [← halls_marriage]
  constructor
  · rintro ⟨M, hM⟩
    have key : ∀ a : L, ∃ b : R, M.Adj (Sum.inl a) (Sum.inr b) := by
      intro a
      obtain ⟨w, hw, -⟩ := hM.1 (hM.2 (Sum.inl a))
      match w, hw with
      | Sum.inr b, hw => exact ⟨b, hw⟩
      | Sum.inl c, hw => exact absurd (M.adj_sub hw) not_false
    choose f hf using key
    refine ⟨f, ?_, fun a => M.adj_sub (hf a)⟩
    intro a a' haa'
    obtain ⟨w, -, hu⟩ := hM.1 (hM.2 (Sum.inr (f a)))
    have h1 : Sum.inl a = w := hu _ (M.symm (hf a))
    have h2 : Sum.inl a' = w := hu _ (M.symm (haa' ▸ hf a'))
    exact Sum.inl_injective (h1.trans h2.symm)
  · rintro ⟨f, hfinj, hfr⟩
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩
    set e : L ≃ R := Equiv.ofBijective f hbij with he
    set σ : (L ⊕ R) → (L ⊕ R) :=
      Sum.elim (fun a => Sum.inr (e a)) (fun b => Sum.inl (e.symm b)) with hσ
    have hinv : ∀ u, σ (σ u) = u := by rintro (a | b) <;> simp [hσ]
    have hadj : ∀ u, (bipartiteGraph r).Adj u (σ u) := by
      rintro (a | b)
      · exact hfr a
      · have : f (e.symm b) = b := e.apply_symm_apply b
        simpa [hσ, bipartiteGraph, this] using hfr (e.symm b)
    refine ⟨{ verts := Set.univ
              Adj := fun u v => v = σ u
              adj_sub := by rintro u v rfl; exact hadj u
              edge_vert := fun _ => trivial
              symm := by rintro u v rfl; exact (hinv u).symm }, ?_, fun _ => trivial⟩
    intro v _
    exact ⟨σ v, rfl, fun _ hy => hy⟩

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

