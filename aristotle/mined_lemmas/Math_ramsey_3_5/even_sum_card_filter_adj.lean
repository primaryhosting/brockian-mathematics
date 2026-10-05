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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

lemma even_sum_card_filter_adj (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Even (∑ v ∈ S, #{w ∈ S | G.Adj v w}) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
      have hxx : ¬ G.Adj x x := G.irrefl
      have h1 : {w ∈ insert x S | G.Adj x w} = {w ∈ S | G.Adj x w} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, ha⟩
          · exact absurd ha hxx
          · exact ⟨hw, ha⟩
        · rintro ⟨hw, ha⟩; exact ⟨Or.inr hw, ha⟩
      have h2 : ∀ v ∈ S, #{w ∈ insert x S | G.Adj v w}
          = #{w ∈ S | G.Adj v w} + (if G.Adj v x then 1 else 0) := by
        intro v hv
        by_cases hvx : G.Adj v x
        · have : {w ∈ insert x S | G.Adj v w} = insert x {w ∈ S | G.Adj v w} := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, ha⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hw, ha⟩
            · rintro (rfl | ⟨hw, ha⟩)
              · exact ⟨Or.inl rfl, hvx⟩
              · exact ⟨Or.inr hw, ha⟩
          rw [this, Finset.card_insert_of_notMem (by simp [hx]), if_pos hvx]
        · have : {w ∈ insert x S | G.Adj v w} = {w ∈ S | G.Adj v w} := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, ha⟩
              · exact absurd ha hvx
              · exact ⟨hw, ha⟩
            · rintro ⟨hw, ha⟩; exact ⟨Or.inr hw, ha⟩
          rw [this, if_neg hvx, Nat.add_zero]
      have h3 : ∑ v ∈ S, (if G.Adj v x then 1 else 0) = #{w ∈ S | G.Adj x w} := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun v _ => if_congr (G.adj_comm v x) rfl rfl)
      rw [Finset.sum_insert hx, h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, h3]
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + #{w ∈ S | G.Adj x w}, by omega⟩

/-! ### The Ramsey upper bounds -/

