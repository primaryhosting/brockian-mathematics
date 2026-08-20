import RequestProject.Ramsey
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

import Mathlib

/-!
# The Ramsey number `R(4,4) = 18`

We define two-colourings of the edges of a complete graph as simple graphs (`red` = adjacent,
`blue` = non-adjacent), and prove that every graph on 18 vertices contains a red or a blue
clique on 4 vertices, while the Paley graph on 17 vertices contains neither.
-/

open Finset
open scoped Classical

namespace Math

variable {V : Type*} {G : SimpleGraph V} {S S' : Finset V} {s t : ℕ} {v : V}

/-- `A` is a set of vertices, all pairs of which are adjacent (a "red" clique). -/

lemma even_sum_card_redN (G : SimpleGraph V) (S : Finset V) :
    Even (∑ v ∈ S, (redN G S v).card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      have key : ∀ v ∈ T, (redN G (insert a T) v).card
          = (redN G T v).card + (if G.Adj v a then 1 else 0) := by
        intro v _
        by_cases hva : G.Adj v a
        · have : redN G (insert a T) v = insert a (redN G T v) := by
            ext y; simp only [mem_redN, Finset.mem_insert]
            constructor
            · rintro ⟨hy | hy, h2⟩
              · exact Or.inl hy
              · exact Or.inr ⟨hy, h2⟩
            · rintro (rfl | ⟨hy, h2⟩)
              · exact ⟨Or.inl rfl, hva⟩
              · exact ⟨Or.inr hy, h2⟩
          rw [this, Finset.card_insert_of_notMem (fun hc => ha ((mem_redN (G := G)).1 hc).1),
            if_pos hva]
        · have : redN G (insert a T) v = redN G T v := by
            ext y; simp only [mem_redN, Finset.mem_insert]
            constructor
            · rintro ⟨hy | hy, h2⟩
              · subst hy; exact absurd h2 hva
              · exact ⟨hy, h2⟩
            · rintro ⟨hy, h2⟩; exact ⟨Or.inr hy, h2⟩
          rw [this, if_neg hva, Nat.add_zero]
      have hA : redN G (insert a T) a = redN G T a := by
        ext y; simp only [mem_redN, Finset.mem_insert]
        constructor
        · rintro ⟨hy | hy, h2⟩
          · subst hy; exact absurd rfl (G.ne_of_adj h2)
          · exact ⟨hy, h2⟩
        · rintro ⟨hy, h2⟩; exact ⟨Or.inr hy, h2⟩
      have hsum : ∑ v ∈ T, (if G.Adj v a then 1 else 0) = (redN G T a).card := by
        have heq : T.filter (fun v => G.Adj v a) = T.filter (fun y => G.Adj a y) :=
          Finset.filter_congr (fun x _ => by rw [SimpleGraph.adj_comm])
        rw [← Finset.card_filter, heq]
        rfl
      rw [Finset.sum_insert ha, hA, Finset.sum_congr rfl key, Finset.sum_add_distrib, hsum]
      have : (redN G T a).card + (∑ v ∈ T, (redN G T v).card + (redN G T a).card)
          = (∑ v ∈ T, (redN G T v).card) + 2 * (redN G T a).card := by ring
      rw [this]
      exact ih.add (even_two_mul _)

