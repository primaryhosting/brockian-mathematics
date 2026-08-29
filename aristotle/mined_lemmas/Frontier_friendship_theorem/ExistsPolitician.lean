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

def ExistsPolitician (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

variable [Fintype V] {G : SimpleGraph V} {d : ℕ}

section Basic

/-- In a friendship graph, the off-diagonal entries of the square of the adjacency matrix
are all `1`: they count the (unique) length-two walks between distinct vertices. -/
