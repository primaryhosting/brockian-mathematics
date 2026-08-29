/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring, since Lean
-- requires `import` to be the first command in a file.)

import Mathlib

/-!
## Notes on provenance of the argument

The statement below is the Erdős–Rényi–Sós friendship theorem.  Mathlib contains a proof of
it in its *Archive* (not in the main library): `Theorems100.friendship_theorem` in
`Archive/Wiedijk100Theorems/FriendshipGraphs.lean`, due to Aaron Anderson, Jalex Stark and
Kyle Miller (Apache 2.0).  Since the Archive is not part of the `Mathlib` library that this
project imports, the development is reproduced here, adapted into the `Frontier` namespace,
so that `Frontier.friendship_theorem` is self-contained on top of `Mathlib`.

The proof runs through adjacency matrices:
* nonadjacent vertices of a friendship graph have equal degree;
* hence a friendship graph with no "politician" (a vertex adjacent to all others) is regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* for `d ≤ 2` one exhibits a politician directly;
* for `3 ≤ d`, taking a prime `p ∣ d - 1`, the adjacency matrix over `ZMod p` has trace `0`
  but its `p`-th power has trace `1`, contradicting `ZMod.trace_pow_card`.
-/

open scoped BigOperators
open scoped Classical

namespace Frontier

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

/-- A graph is a *friendship graph* when every pair of distinct vertices has exactly one
common neighbour. -/

theorem isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Frontier.ExistsPolitician] at hG'
  push_neg at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, G.symm hxw⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, G.symm hcontra⟩)]

include hG in
/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
