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

