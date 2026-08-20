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

@[simp] lemma surfaceOfCounts_numVertices (v f : ℕ) (hv : 0 < v) (hf : 0 < f) :
    (surfaceOfCounts v f hv hf).numVertices = v := by
  simp [surfaceOfCounts, PolyhedralSurface.numVertices]

