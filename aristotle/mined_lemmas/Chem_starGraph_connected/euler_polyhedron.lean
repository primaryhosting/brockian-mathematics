import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open SimpleGraph

/-! ### Star graphs are trees

We need a supply of concrete finite trees in order to exhibit examples of the
structure defined below; the simplest such family is the star graph. -/

/-- The star graph on `V` centred at `c`: `a` and `b` are adjacent iff they are
distinct and one of them is the centre `c`. -/

theorem euler_polyhedron (P : PolyhedralSurface) :
    (P.numVertices : ℤ) - P.numEdges + P.numFaces = 2 := by
  have hV : Nat.card P.primalTree.edgeSet + 1 = Nat.card P.Vertex :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.primalTree_isTree).2
  have hF : Nat.card P.dualTree.edgeSet + 1 = Nat.card P.Face :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.dualTree_isTree).2
  have hE := P.edge_partition
  simp only [PolyhedralSurface.numVertices, PolyhedralSurface.numEdges,
    PolyhedralSurface.numFaces]
  omega

/-- Euler's formula, stated in `ℕ` as `V + F = E + 2`. -/
