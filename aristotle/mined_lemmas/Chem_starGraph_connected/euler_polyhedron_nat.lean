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

theorem euler_polyhedron_nat (P : PolyhedralSurface) :
    P.numVertices + P.numFaces = P.numEdges + 2 := by
  have := euler_polyhedron P
  omega

/-! ### Examples: the hypotheses are satisfiable -/

/-- Any counts `V, F ≥ 1` with `E = V + F - 2` are realised by a polyhedral
surface, so the hypotheses of `Chem.euler_polyhedron` are satisfiable. -/
