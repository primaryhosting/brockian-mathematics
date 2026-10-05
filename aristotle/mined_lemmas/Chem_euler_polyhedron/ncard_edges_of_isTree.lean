import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A convex polyhedron (for instance a fullerene cage such as C₆₀) gives rise to a *plane map*:

* a graph `G` on the set `Vt` of vertices;
* the dual graph `D` on the set `Ft` of faces;
* a bijection `dual` between the edges of `G` and the edges of `D` — each edge of the
  polyhedron is shared by exactly two faces, and dually.

Planarity (i.e. the fact that the map lives on a sphere) is encoded by the classical
*interdigitating spanning trees* property: there is a spanning tree `T` of the graph such
that the duals of the remaining edges form a spanning tree of the dual graph.  This is the
combinatorial content of planarity used in the standard proof of Euler's formula, and it is
the hypothesis of `Chem.euler_polyhedron` below, whose conclusion is `V - E + F = 2`.

The hypotheses are not vacuous: `Chem.tetrahedron_euler` verifies them for the tetrahedron
(whose graph and dual graph are both `K₄`), and `Chem.fullerene_twelve_pentagons` derives
from Euler's formula the chemical fact that a trivalent cage whose faces are pentagons and
hexagons has exactly twelve pentagons.
-/

namespace Chem

open SimpleGraph

/-- For a set `S` of edges of a graph `H` spanning a tree, `#S + 1 = #vertices`. -/

private theorem ncard_edges_of_isTree {A : Type*} [Finite A] (H : SimpleGraph A)
    (S : Set (Sym2 A)) (hS : S ⊆ H.edgeSet) (h : (SimpleGraph.fromEdgeSet S).IsTree) :
    S.ncard + 1 = Nat.card A := by
  have h2 := (SimpleGraph.isTree_iff_connected_and_card).1 h
  have he : (SimpleGraph.fromEdgeSet S).edgeSet = S := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    exact ⟨fun h => h.1, fun h => ⟨h, H.not_isDiag_of_mem_edgeSet (hS h)⟩⟩
  rw [he] at h2
  exact h2.2

/-- **Euler's polyhedron formula** `V - E + F = 2`.

`G` is the graph of the polyhedron on the vertex set `Vt`, `D` is its dual graph on the set
`Ft` of faces, and `dual` matches up the edges of `G` with the edges of `D`.  The planarity
of the map is expressed through the interdigitating spanning trees `T` (of `G`) and
`dual '' (E \ T)` (of `D`). -/
