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
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem exists_politician_of_degree_eq_two (hG : UniqueCommonFriend G) [Nonempty V]
    (hd : G.IsRegularOfDegree 2) : ∃ v : V, IsPolitician G v := by
  have h := card_of_regular hG hd
  have hn : Fintype.card V = 3 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  refine ⟨Classical.arbitrary V, fun w hw => ?_⟩
  set v := Classical.arbitrary V with hv
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro x hx
    rw [mem_neighborFinset] at hx
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
  have hcards : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_neighborFinset_eq_degree, hd v,
      Finset.card_univ, hn]
  have heq : G.neighborFinset v = Finset.univ.erase v := Finset.eq_of_subset_of_card_le hsub hcards
  rw [← mem_neighborFinset, heq]
  exact Finset.mem_erase.mpr ⟨hw.symm, Finset.mem_univ _⟩

