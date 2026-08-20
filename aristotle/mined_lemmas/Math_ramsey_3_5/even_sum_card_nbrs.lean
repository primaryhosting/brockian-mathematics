import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Cliques and independent sets inside a finite set of vertices -/

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V} {n : ℕ} {v : V}

/-- `CliqueOn G s n` : the vertex set `s` contains a clique of `G` with `n` vertices. -/

lemma even_sum_card_nbrs (s : Finset V) :
    Even (∑ v ∈ s, (nbrs G s v).card) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have key : ∀ v ∈ t, (nbrs G (insert a t) v).card
          = (nbrs G t v).card + (if G.Adj v a then 1 else 0) := by
        intro v _
        by_cases h : G.Adj v a
        · have : nbrs G (insert a t) v = insert a (nbrs G t v) := by
            ext w; simp only [mem_nbrs, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hw, hadj⟩
            · rintro (rfl | ⟨hw, hadj⟩)
              · exact ⟨Or.inl rfl, h⟩
              · exact ⟨Or.inr hw, hadj⟩
          rw [this, Finset.card_insert_of_notMem (fun hmem => ha (mem_nbrs.mp hmem).1), if_pos h]
        · have : nbrs G (insert a t) v = nbrs G t v := by
            ext w; simp only [mem_nbrs, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact absurd hadj h
              · exact ⟨hw, hadj⟩
            · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
          rw [this, if_neg h, Nat.add_zero]
      have hA : (nbrs G (insert a t) a).card = (nbrs G t a).card := by
        congr 1
        ext w; simp only [mem_nbrs, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hadj⟩
          · exact absurd hadj G.irrefl
          · exact ⟨hw, hadj⟩
        · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
      rw [Finset.sum_insert ha, Finset.sum_congr rfl key, Finset.sum_add_distrib, hA]
      have hfin : ∑ v ∈ t, (if G.Adj v a then 1 else 0) = (nbrs G t a).card := by
        rw [nbrs, Finset.card_filter]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [G.adj_comm w a]
      rw [hfin]
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + (nbrs G t a).card, by omega⟩

end Parity

/-! ## The upper bounds -/

section Bounds

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V}

