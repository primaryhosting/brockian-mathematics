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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

/-! ## Basic notions: cliques and independent sets relative to a finite vertex set -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `IsCl G t` says that the finite set `t` is a clique of `G`. -/

lemma even_sum_deg (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Even (∑ v ∈ s, (Nb G s v).card) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa : Nb G (insert a s) a = Nb G s a := by
      unfold Nb
      rw [Finset.filter_insert, if_neg G.irrefl]
    have hd : ∀ v ∈ s, (Nb G (insert a s) v).card
        = (Nb G s v).card + (if G.Adj v a then 1 else 0) := by
      intro v _
      unfold Nb
      rw [Finset.filter_insert]
      by_cases h : G.Adj v a
      · rw [if_pos h, if_pos h,
          Finset.card_insert_of_notMem (fun hmem => ha (Finset.mem_filter.mp hmem).1)]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hswap : ∑ v ∈ s, (if G.Adj v a then 1 else 0) = (Nb G s a).card := by
      rw [Nb, Finset.card_filter]
      exact Finset.sum_congr rfl
        (fun v _ => if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl)
    rw [Finset.sum_insert ha, hfa, Finset.sum_congr rfl hd, Finset.sum_add_distrib, hswap]
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + (Nb G s a).card, by omega⟩

end Deg

/-! ## The Ramsey upper bounds -/

/-- `R(3,2) ≤ 3`: three vertices contain a triangle or two non-adjacent vertices. -/
