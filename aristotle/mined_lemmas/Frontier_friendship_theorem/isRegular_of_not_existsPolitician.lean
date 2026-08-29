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

theorem isRegular_of_not_existsPolitician (hG : Friendship G) (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  refine ⟨G.degree v, fun x => ?_⟩
  by_cases hvx : G.Adj v x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  rw [ExistsPolitician] at hG'
  push_neg at hG'
  obtain ⟨w, hvw', hvw⟩ := hG' v
  obtain ⟨y, hxy', hxy⟩ := hG' x
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  by_cases hvy : G.Adj v y
  swap
  · rw [degree_eq_of_not_adj hG hvy]
    exact degree_eq_of_not_adj hG hxy
  -- the remaining case is impossible: `x` and `y` would be two common neighbours of `v` and `w`
  have hwy : ¬G.Adj w y := by
    intro hcontra
    exact hxy' (eq_of_mem_commonNeighbors hG hvw'
      ((mem_commonNeighbors G).2 ⟨hvx, G.symm hxw⟩)
      ((mem_commonNeighbors G).2 ⟨hvy, hcontra⟩))
  rw [degree_eq_of_not_adj hG hvw, degree_eq_of_not_adj hG hwy]
  exact degree_eq_of_not_adj hG hxy

/-- Counting length-two walks starting at a fixed vertex in a `d`-regular friendship graph
shows the graph has `d * d - d + 1` vertices. -/
