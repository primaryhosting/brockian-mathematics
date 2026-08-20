import RequestProject.Friendship
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
# The friendship theorem (Erdős–Rényi–Sós)

If `G` is a finite graph in which every two distinct vertices have exactly one common
neighbour, then `G` has a vertex adjacent to all other vertices (a "politician").

The proof follows the classical argument:
* nonadjacent vertices have equal degrees (a length-3 walk count);
* hence a friendship graph with no politician is `d`-regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* the cases `d ≤ 2` are handled directly;
* for `d ≥ 3` we pick a prime `p ∣ d - 1` and compare two computations of the trace of
  `A ^ p`, where `A` is the adjacency matrix over `ZMod p`.
-/

namespace Frontier

open Finset SimpleGraph Matrix

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem hasPolitician_of_degree_le_two [Nonempty V] (hG : IsFriendship G)
    (hd : G.IsRegularOfDegree d) (h : d ≤ 2) : HasPolitician G := by
  have hc := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  interval_cases d
  · -- `d = 0`: at most one vertex
    refine ⟨Classical.arbitrary V, fun w hw => absurd ?_ hw⟩
    have : Fintype.card V ≤ 1 := by omega
    exact Fintype.card_le_one_iff.mp this _ _
  · -- `d = 1`: at most one vertex
    refine ⟨Classical.arbitrary V, fun w hw => absurd ?_ hw⟩
    have : Fintype.card V ≤ 1 := by omega
    exact Fintype.card_le_one_iff.mp this _ _
  · -- `d = 2`: three vertices, and each vertex is adjacent to the two others
    have hV : Fintype.card V = 3 := by omega
    refine ⟨Classical.arbitrary V, fun w hw => ?_⟩
    set v := Classical.arbitrary V
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro x hx
      rw [mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
    have hcards : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_neighborFinset_eq_degree, hd v,
        Finset.card_univ, hV]
    have heq : G.neighborFinset v = Finset.univ.erase v :=
      Finset.eq_of_subset_of_card_le hsub hcards
    have : w ∈ G.neighborFinset v := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨hw.symm, Finset.mem_univ _⟩
    rwa [mem_neighborFinset] at this

end Regular

/-- **The friendship theorem** (Erdős–Rényi–Sós): in a finite nonempty graph in which every two
distinct vertices have exactly one common neighbour, some vertex is adjacent to all others. -/
