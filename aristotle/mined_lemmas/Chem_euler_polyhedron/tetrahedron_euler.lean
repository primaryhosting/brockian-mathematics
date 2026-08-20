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

theorem tetrahedron_euler :
    (Nat.card (Fin 4) : ℤ) - Nat.card (⊤ : SimpleGraph (Fin 4)).edgeSet + Nat.card (Fin 4) = 2 :=
  euler_polyhedron le_top le_top tetraTree_isTree tetraTree_compl_isTree (Equiv.refl _)
    (by decide)

/-- **Fullerenes have exactly twelve pentagonal faces.**

If a polyhedral cage satisfies Euler's formula, every vertex has degree three (`3V = 2E`, the
usual chemical bonding pattern of a fullerene) and every face is a pentagon or a hexagon
(`p` pentagons and `h` hexagons, so `5p + 6h = 2E` and `p + h = F`), then `p = 12`. -/
