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
