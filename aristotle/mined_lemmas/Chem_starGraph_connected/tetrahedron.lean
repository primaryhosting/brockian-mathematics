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

noncomputable def tetrahedron : PolyhedralSurface := surfaceOfCounts 4 4 (by norm_num) (by norm_num)

example : tetrahedron.numVertices = 4 ∧ tetrahedron.numEdges = 6 ∧ tetrahedron.numFaces = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [tetrahedron]

/-- The buckminsterfullerene cage C₆₀: `V = 60`, `E = 90`, `F = 32`
(12 pentagons and 20 hexagons). -/
