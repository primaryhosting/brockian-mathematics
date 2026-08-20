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

variable {L R : Type*}

/-- The bipartite graph on `L ⊕ R` whose edges are exactly the pairs `(a, b)` with `r a b`,
where `a : L` is a left vertex and `b : R` is a right vertex. -/
def bipartiteGraph (r : L → R → Prop) : SimpleGraph (L ⊕ R) where
  Adj x y := match x, y with
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  symm := by rintro (a | b) (a' | b') h <;> simp_all
  loopless := by constructor; rintro (a | b) <;> simp

@[simp] lemma bipartiteGraph_adj_inl_inr (r : L → R → Prop) (a : L) (b : R) :
    (bipartiteGraph r).Adj (.inl a) (.inr b) ↔ r a b := Iff.rfl

@[simp] lemma bipartiteGraph_adj_inr_inl (r : L → R → Prop) (a : L) (b : R) :
    (bipartiteGraph r).Adj (.inr b) (.inl a) ↔ r a b := Iff.rfl

@[simp] lemma bipartiteGraph_not_adj_inl_inl (r : L → R → Prop) (a a' : L) :
    ¬ (bipartiteGraph r).Adj (.inl a) (.inl a') := id

@[simp] lemma bipartiteGraph_not_adj_inr_inr (r : L → R → Prop) (b b' : R) :
    ¬ (bipartiteGraph r).Adj (.inr b) (.inr b') := id

/-- A bipartite graph given by `r` has a perfect matching iff there is a bijection
`e : L ≃ R` with `r a (e a)` for all `a`. -/
theorem exists_isPerfectMatching_iff_exists_equiv (r : L → R → Prop) :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔
      ∃ e : L ≃ R, ∀ a, r a (e a) := by
  constructor
  · rintro ⟨M, hmatch, hspan⟩
    have key : ∀ a : L, ∃! b : R, M.Adj (.inl a) (.inr b) := by
      intro a
      obtain ⟨w, hw, huniq⟩ := hmatch (hspan (.inl a))
      cases w with
      | inl a' =>
          exact absurd (M.adj_sub hw) (bipartiteGraph_not_adj_inl_inl r a a')
      | inr b =>
          refine ⟨b, hw, fun b' hb' => ?_⟩
          have := huniq (.inr b') hb'
          exact (Sum.inr.injEq b' b ▸ this)
    set f : L → R := fun a => (key a).choose
    have hf : ∀ a, M.Adj (.inl a) (.inr (f a)) := fun a => (key a).choose_spec.1
    have hinj : Function.Injective f := by
      intro a a' h
      obtain ⟨w, _, huniq⟩ := hmatch (hspan (.inr (f a)))
      have h1 := huniq (.inl a) (M.symm (hf a))
      have h2 := huniq (.inl a') (M.symm (h ▸ hf a'))
      exact Sum.inl.inj (h1.trans h2.symm)
    have hsurj : Function.Surjective f := by
      intro b
      obtain ⟨w, hw, _⟩ := hmatch (hspan (.inr b))
      cases w with
      | inl a =>
          exact ⟨a, ((key a).choose_spec.2 b (M.symm hw)).symm⟩
      | inr b' =>
          exact absurd (M.adj_sub hw) (bipartiteGraph_not_adj_inr_inr r b b')
    exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun a => M.adj_sub (hf a)⟩
  · rintro ⟨e, he⟩
    refine ⟨{ verts := Set.univ
              Adj := fun x y => match x, y with
                | .inl a, .inr b => e a = b
                | .inr b, .inl a => e a = b
                | _, _ => False
              adj_sub := ?_
              edge_vert := ?_
              symm := ?_ }, ?_, ?_⟩
    · rintro (a | b) (a' | b') h
      · exact h.elim
      · simp only at h
        subst h
        exact he a
      · simp only at h
        subst h
        exact he a'
      · exact h.elim
    · intro v w _
      trivial
    · rintro (a | b) (a' | b') h <;> simp_all
    · rintro (a | b) _
      · refine ⟨.inr (e a), rfl, ?_⟩
        rintro (a' | b') h
        · exact h.elim
        · simp only at h
          exact congrArg Sum.inr h.symm
      · refine ⟨.inl (e.symm b), by simp, ?_⟩
        rintro (a' | b') h
        · simp only at h
          exact congrArg Sum.inl (by rw [← h, Equiv.symm_apply_apply])
        · exact h.elim
    · intro v; trivial

/-- Hall's condition on both sides is equivalent to the existence of a matching bijection. -/
theorem exists_equiv_iff_hall [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (r : L → R → Prop) [DecidableRel r] :
    (∃ e : L ≃ R, ∀ a, r a (e a)) ↔
      ((∀ A : Finset L, #A ≤ #{b : R | ∃ a ∈ A, r a b}) ∧
        (∀ B : Finset R, #B ≤ #{a : L | ∃ b ∈ B, r a b})) := by
  constructor
  · rintro ⟨e, he⟩
    constructor
    · intro A
      rw [← Finset.card_image_of_injective A e.injective]
      refine Finset.card_le_card ?_
      intro b hb
      simp only [Finset.mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, he a⟩
    · intro B
      rw [← Finset.card_image_of_injective B e.symm.injective]
      refine Finset.card_le_card ?_
      intro a ha
      simp only [Finset.mem_image] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hb, ?_⟩
      simpa using he (e.symm b)
  · rintro ⟨hL, hR⟩
    obtain ⟨f, hf, hfr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hL
    obtain ⟨g, hg, hgr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective (fun b a => r a b)).mp hR
    have hcard : Fintype.card L = Fintype.card R :=
      le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    exact ⟨Equiv.ofBijective f hbij, fun a => hfr a⟩

/-- **Hall's Marriage Theorem** for bipartite graphs: the bipartite graph on `L ⊕ R` determined
by the relation `r` has a perfect matching if and only if Hall's condition holds on both sides,
i.e. every set of left vertices has at least as many neighbours, and likewise for the right. -/
theorem halls_marriage [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (r : L → R → Prop) [DecidableRel r] :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔
      ((∀ A : Finset L, #A ≤ #{b : R | ∃ a ∈ A, r a b}) ∧
        (∀ B : Finset R, #B ≤ #{a : L | ∃ b ∈ B, r a b})) :=
  (exists_isPerfectMatching_iff_exists_equiv r).trans (exists_equiv_iff_hall r)

end Math

section Examples

/-- Sanity check (non-vacuity): the complete bipartite graph `K_{2,2}` has a perfect matching. -/
example : ∃ M : (Math.bipartiteGraph (fun _ _ : Fin 2 => True)).Subgraph, M.IsPerfectMatching :=
  (Math.halls_marriage _).mpr ⟨by decide, by decide⟩

/-- Sanity check (non-vacuity): the edgeless bipartite graph on `Fin 1 ⊕ Fin 1` has no perfect
matching, since Hall's condition fails. -/
example : ¬ ∃ M : (Math.bipartiteGraph (fun _ _ : Fin 1 => False)).Subgraph,
    M.IsPerfectMatching := fun h => absurd ((Math.halls_marriage _).mp h) (by decide)

end Examples

#print axioms Math.halls_marriage

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

