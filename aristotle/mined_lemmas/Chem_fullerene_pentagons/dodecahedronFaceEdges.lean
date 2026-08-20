import Mathlib

/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

/-! ### Combinatorial model of a trivalent polyhedron -/

/--
A **trivalent polyhedron**, combinatorially: finite types of vertices, edges and faces
together with the incidence maps `edgeEnds` (endpoints of an edge) and `faceEdges` (edges
bounding a face), subject to

* `card_edgeEnds`      : every edge has exactly two endpoints;
* `trivalent`          : every vertex lies on exactly three edges;
* `card_faces_of_edge` : every edge lies on exactly two faces;
* `euler`              : Euler's formula `V - E + F = 2`, stated subtraction-free.
-/
structure TrivalentPolyhedron where
  /-- The vertices. -/
  Vert : Type
  /-- The edges. -/
  Edge : Type
  /-- The faces. -/
  Face : Type
  [fintypeVert : Fintype Vert]
  [fintypeEdge : Fintype Edge]
  [fintypeFace : Fintype Face]
  [decEqVert : DecidableEq Vert]
  [decEqEdge : DecidableEq Edge]
  /-- The set of endpoints of an edge. -/
  edgeEnds : Edge → Finset Vert
  /-- The set of edges bounding a face. -/
  faceEdges : Face → Finset Edge
  /-- Every edge has exactly two endpoints. -/
  card_edgeEnds : ∀ e, (edgeEnds e).card = 2
  /-- Every vertex lies on exactly three edges. -/
  trivalent : ∀ v, (univ.filter fun e => v ∈ edgeEnds e).card = 3
  /-- Every edge lies on exactly two faces. -/
  card_faces_of_edge : ∀ e, (univ.filter fun f => e ∈ faceEdges f).card = 2
  /-- Euler's formula `V - E + F = 2`, written without subtraction. -/
  euler : Fintype.card Vert + Fintype.card Face = Fintype.card Edge + 2

attribute [instance] TrivalentPolyhedron.fintypeVert TrivalentPolyhedron.fintypeEdge
  TrivalentPolyhedron.fintypeFace TrivalentPolyhedron.decEqVert TrivalentPolyhedron.decEqEdge

/--
A **fullerene**: a trivalent polyhedron all of whose faces are pentagons or hexagons.
This is the standard combinatorial model of a fullerene molecule, whose carbon atoms are
the vertices and whose bonds are the edges.
-/
structure Fullerene extends TrivalentPolyhedron where
  /-- Every face is bounded by five or by six edges. -/
  pentagon_or_hexagon : ∀ f : Face, (faceEdges f).card = 5 ∨ (faceEdges f).card = 6

/-- Double counting of a relation between two finite types: summing the row sizes and
summing the column sizes give the same total. -/

def dodecahedronFaceEdges : Fin 12 → Finset (Fin 30) :=
  ![{1, 2, 3, 5, 26}, {0, 2, 6, 8, 24}, {0, 1, 12, 13, 25}, {4, 5, 10, 11, 27},
    {3, 4, 15, 16, 25}, {6, 7, 9, 10, 26}, {7, 8, 18, 20, 28}, {9, 11, 21, 22, 28},
    {13, 14, 16, 17, 29}, {12, 14, 18, 19, 24}, {15, 17, 21, 23, 27}, {19, 20, 22, 23, 29}]

/-- The regular dodecahedron as a fullerene: all incidence conditions are checked by
decision procedure on the explicit combinatorial data. -/
