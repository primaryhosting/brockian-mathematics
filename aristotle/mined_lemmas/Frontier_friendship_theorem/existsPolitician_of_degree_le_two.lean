import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Erdős–Rényi–Sós friendship theorem: in a finite graph in which every two distinct
vertices have exactly one common neighbour, there is a vertex adjacent to all others.

The proof follows the classical adjacency-matrix argument:
* the square of the adjacency matrix has all off-diagonal entries equal to `1`;
* non-adjacent vertices have equal degrees;
* without a politician the graph is regular, of some degree `d`;
* counting gives `d + (n - 1) = d * d` where `n` is the number of vertices;
* `d ≤ 2` forces a politician directly;
* for `d ≥ 3` one takes a prime `p ∣ d - 1` and computes the trace of the `p`-th power of
  the adjacency matrix over `ZMod p` in two ways, obtaining `0 = 1`.
-/

open Finset SimpleGraph Matrix

namespace Frontier

noncomputable section

open scoped Classical

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

/-- The hypothesis of the friendship theorem: every pair of distinct vertices has exactly
one common neighbour. -/

theorem existsPolitician_of_degree_le_two (hG : Friendship G) (hd : G.IsRegularOfDegree d)
    (h : d ≤ 2) : ExistsPolitician G := by
  have hcard := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  interval_cases d
  · have hle : Fintype.card V ≤ 1 := by omega
    exact ⟨Classical.arbitrary V, fun w hvw =>
      absurd (Fintype.card_le_one_iff.1 hle _ w) hvw⟩
  · have hle : Fintype.card V ≤ 1 := by omega
    exact ⟨Classical.arbitrary V, fun w hvw =>
      absurd (Fintype.card_le_one_iff.1 hle _ w) hvw⟩
  · -- a `2`-regular friendship graph is a triangle
    have hn : Fintype.card V = 3 := by omega
    set v := Classical.arbitrary V
    have hsub : G.neighborFinset v ⊆ univ.erase v := by
      intro x hx
      rw [mem_neighborFinset] at hx
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hx).symm, mem_univ _⟩
    have hcard2 : (univ.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, hn]
    have hnb : G.neighborFinset v = univ.erase v :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [hcard2, card_neighborFinset_eq_degree, hd v])
    refine ⟨v, fun w hvw => ?_⟩
    rw [← mem_neighborFinset, hnb, Finset.mem_erase]
    exact ⟨hvw.symm, mem_univ _⟩

end SmallDegree

section LargeDegree

variable [Nonempty V]

omit [Nonempty V] in
/-- Modulo a prime factor `p` of `d - 1`, all powers `≥ 2` of the adjacency matrix of a
`d`-regular friendship graph are the all-ones matrix. -/
