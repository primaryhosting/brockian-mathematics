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

theorem sum_card_faceEdges_eq :
    ∑ f : P.Face, (P.faceEdges f).card = 5 * P.pentagons.card + 6 * P.hexagons.card := by
  classical
  have hsplit : (univ : Finset P.Face) = P.pentagons ∪ P.hexagons := by
    apply (Finset.eq_univ_of_forall ?_).symm
    intro f
    rcases P.pentagon_or_hexagon f with h | h
    · exact Finset.mem_union_left _ (by simp [pentagons, h])
    · exact Finset.mem_union_right _ (by simp [hexagons, h])
  have hdisj : Disjoint P.pentagons P.hexagons := by
    simp only [pentagons, hexagons]
    rw [Finset.disjoint_filter]
    intro f _ h5
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have h5 : ∑ f ∈ P.pentagons, (P.faceEdges f).card = 5 * P.pentagons.card := by
    rw [Finset.sum_congr rfl (fun f hf => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    simpa [pentagons] using hf
  have h6 : ∑ f ∈ P.hexagons, (P.faceEdges f).card = 6 * P.hexagons.card := by
    rw [Finset.sum_congr rfl (fun f hf => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    simpa [hexagons] using hf
  rw [h5, h6]

end Fullerene

/-! ### The arithmetic core -/

/--
The purely arithmetic content of the theorem: from Euler's formula, trivalence, the
splitting of the faces into pentagons and hexagons, and the face–edge incidence count,
the number of pentagons is forced to be `12`.
-/
