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

noncomputable def numFaces : ℕ := Nat.card P.Face

end PolyhedralSurface

/-- **Euler's polyhedron formula**: for a convex polyhedron (for instance a
fullerene cage), `V - E + F = 2`.

The proof is the tree–cotree argument: a spanning tree of the graph has
`V - 1` edges and a spanning tree of the dual graph has `F - 1` edges
(`SimpleGraph.IsTree.card_edgeFinset`, used here in its `Nat.card` form
`SimpleGraph.isTree_iff_connected_and_card`), and together they use up all `E`
edges. -/
