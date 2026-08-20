import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

/-!
## Euler's polyhedron formula `V - E + F = 2`

A convex polyhedron (a fullerene cage, say) is described combinatorially by its
*skeleton* `G` — the graph of vertices and edges — together with its *dual graph* `D`,
whose nodes are the faces of the polyhedron and whose edges record which pairs of
faces share an edge of the polyhedron.  Each edge of the polyhedron is at the same
time an edge of `G` and an edge of `D`, which is recorded by the bijection
`dualEdge : G.edgeSet ≃ D.edgeSet`.

The fact that the surface of the polyhedron is a *sphere* (and not, say, a torus)
is expressed by the classical **tree–cotree** (spanning tree / dual spanning tree)
decomposition: there is a spanning tree `T` of the skeleton such that the edges *not*
in `T` are exactly the edges whose duals form a spanning tree `C` of the dual graph.
Both of these are genuine spanning trees, i.e. connected and acyclic graphs on the
whole vertex (resp. face) set.

From this data Euler's formula `V - E + F = 2` follows: the primal tree has `V - 1`
edges, the dual tree has `F - 1` edges, and every edge lies in exactly one of the two
families.
-/

/-- **Euler's polyhedron formula.**  For a polyhedron presented by its skeleton `G`
(vertices `V`, edges `G.edgeFinset`) and dual graph `D` (nodes = faces), with the
sphere condition given by a tree–cotree decomposition `(T, C)`, one has
`V - E + F = 2`. -/

theorem euler_tetrahedron :
    (Fintype.card (Fin 4) : ℤ) - (Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet : ℤ)
      + (Fintype.card (Fin 4) : ℤ) = 2 := by
  have h := euler_polyhedron (⊤ : SimpleGraph (Fin 4)) tetraStar (⊤ : SimpleGraph (Fin 4))
    tetraStar tetraStar_le_top tetraStar_le_top tetraStar_isTree tetraStar_isTree tetraDualEdge
    (by decide)
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

/-- Sanity check on the numbers: the tetrahedron really has `6` edges. -/
example : Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet = 6 := by decide

/-!
## A chemical consequence: every fullerene has exactly 12 pentagons

A fullerene cage is a convex polyhedron all of whose vertices have degree `3`
(each carbon atom has three neighbours) and all of whose faces are pentagons or
hexagons.  Counting incidences gives `2E = 3V` and `2E = 5p + 6h`, where `p` and `h`
are the numbers of pentagonal and hexagonal faces; Euler's formula then forces
`p = 12`, independently of the size of the cage.
-/

/-- **Twelve pentagons.**  For a polyhedron with all vertices of degree three whose
faces are pentagons and hexagons, Euler's formula `V - E + F = 2` forces the number
of pentagons to be exactly `12`. -/
