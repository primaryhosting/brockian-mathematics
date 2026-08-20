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

noncomputable def fullereneC60 : PolyhedralSurface :=
  surfaceOfCounts 60 32 (by norm_num) (by norm_num)

example : fullereneC60.numVertices = 60 ∧ fullereneC60.numEdges = 90 ∧
    fullereneC60.numFaces = 32 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fullereneC60]

/-! ### A chemical corollary: every fullerene has exactly twelve pentagons -/

/-- For a cubic (three-valent) polyhedron all of whose faces are pentagons or
hexagons — a fullerene cage — Euler's formula forces the number of pentagonal
faces to be exactly `12`, whatever the number `h` of hexagons.

Here `cubic` says that every vertex lies on three edges (`3V = 2E`), `faces`
that the `F` faces split into `p` pentagons and `h` hexagons, and `incidences`
counts edge–face incidences (`2E = 5p + 6h`). -/
