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

theorem card_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : (Fintype.card V : ZMod p) = 1 := by
  have hcard := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hdm : d + m = d * d := by omega
  have := congrArg (fun n : ℕ => (n : ZMod p)) hdm
  simp only [Nat.cast_add, Nat.cast_mul, dmod, one_mul] at this
  have hm0 : (m : ZMod p) = 0 := by linear_combination this
  rw [hm, Nat.cast_add, hm0, Nat.cast_one, zero_add]

/-- There is no `d`-regular friendship graph with `3 ≤ d`. -/
