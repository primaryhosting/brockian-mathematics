/-
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
## Euler's polyhedron formula `V - E + F = 2`

A convex polyhedron (for instance a fullerene cage such as C₆₀) is described combinatorially by

* its *1-skeleton* `G`, the simple graph of vertices and edges of the polyhedron;
* its *dual graph* `D`, whose vertices are the faces of the polyhedron and whose edges are in
  bijection with the edges of `G` (an edge of `G` is dual to the edge joining the two faces
  meeting along it).

Planarity of the 1-skeleton of a convex polyhedron (Steinitz) is used, in the classical proof of
Euler's formula, through the *tree–cotree* (spanning tree / dual spanning tree) decomposition:
one can choose a spanning tree `T` of `G` such that the duals of the edges **not** in `T` form a
spanning tree `S` of the dual graph `D`.  This is exactly the hypothesis packaged below, and the
conclusion is Euler's formula

  `#vertices - #edges + #faces = 2`.

The only nontrivial input is the Mathlib lemma
`SimpleGraph.isTree_iff_connected_and_card` (equivalently `SimpleGraph.IsTree.card_edgeFinset`):
a tree on `n` vertices has `n - 1` edges.
-/

namespace Chem

open SimpleGraph

/-- The edges of a subgraph `H ≤ G`, seen as a sub-collection of the edges of `G`. -/

lemma tetraTree_compl_isTree : (tetraTreeᶜ).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨by decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

