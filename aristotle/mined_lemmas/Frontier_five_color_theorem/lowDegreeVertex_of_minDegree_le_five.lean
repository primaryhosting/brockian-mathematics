import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

lemma lowDegreeVertex_of_minDegree_le_five {s : Finset V} {G : SimpleGraph V}
    (hmin : s.Nonempty → ∃ v ∈ s, (nbrs s G v).card ≤ 5) (h6 : NoK6 s G) :
    LowDegreeVertex s G := by
  intro hne
  obtain ⟨v, hv, hdeg⟩ := hmin hne
  rcases le_or_gt (nbrs s G v).card 4 with h | h
  · exact ⟨v, hv, Or.inl h⟩
  refine ⟨v, hv, Or.inr ⟨hdeg, ?_⟩⟩
  by_contra hcon
  push_neg at hcon
  have hvnot : v ∉ nbrs s G v := by simp [mem_nbrs]
  have hKcard : (insert v (nbrs s G v)).card = 6 := by
    rw [Finset.card_insert_of_notMem hvnot]; omega
  have hKsub : insert v (nbrs s G v) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hv
    · exact (mem_nbrs.1 hx).1
  obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := h6 _ hKsub hKcard
  rcases Finset.mem_insert.1 hx with rfl | hx'
  · exact hnadj (mem_nbrs.1 (by simpa [hxy.symm] using hy)).2.2
  · rcases Finset.mem_insert.1 hy with rfl | hy'
    · exact hnadj ((mem_nbrs.1 hx').2.2).symm
    · exact hnadj (hcon x hx' y hy' hxy)

/-- **Five Colour Theorem** (combinatorial core, in terms of degrees and `K₆`).

Let `G` be a finite simple graph with the property that every graph obtained from `G` by
repeatedly deleting vertices and contracting a vertex into two of its non-adjacent neighbours
(both operations preserve planarity) has a vertex of degree at most `5` and contains no `K₆`.
Then `G` is `5`-colourable.

For a planar graph the first hypothesis is exactly the consequence of Euler's formula
(`|E| ≤ 3|V| - 6`, hence a vertex of degree at most `5`) and the second holds because `K₆`
contains the non-planar graph `K₅`.  Deriving these two facts from a formal definition of
planarity is not carried out here; the present statement isolates the combinatorial heart of
the theorem, the Kempe/Wernicke contraction argument. -/
