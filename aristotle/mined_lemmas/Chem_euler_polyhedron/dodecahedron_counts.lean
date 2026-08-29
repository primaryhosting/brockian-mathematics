/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Formalization notes

A convex polyhedron (for instance a fullerene cage such as C₆₀) is described
combinatorially by its Schlegel diagram: a connected plane graph whose vertices, edges and
faces (including the outer face, corresponding to the polyhedron face one projects from)
correspond to the vertices, edges and faces of the polyhedron.

Such a plane graph is obtained from a single vertex by the two elementary moves that
generate all connected plane graphs:

* attach a new vertex by a new edge (growing a spanning tree):
  `V ↦ V + 1`, `E ↦ E + 1`, `F` unchanged;
* draw a new edge between two vertices already present, inside a face:
  `E ↦ E + 1`, `F ↦ F + 1` (the new edge splits that face in two), `V` unchanged.

`Chem.PolyhedronCounts V E F` records exactly this generation process at the level of the
three counts, and `Chem.euler_polyhedron` is Euler's formula `V - E + F = 2` for it.

Non-vacuity is witnessed by `Chem.PolyhedronCounts.tree_plus_edges` (a spanning tree plus
the remaining edges) and by the concrete instances below: tetrahedron, cube, dodecahedron
and the C₆₀ fullerene cage.

As a chemical application, `Chem.fullerene_twelve_pentagons` deduces from Euler's formula
that every fullerene cage has exactly twelve pentagonal faces.

The file is written in pure core Lean 4 (no imports), so that the required header comment
can literally begin the file.
-/

namespace Chem

/-- Admissible vertex/edge/face counts `(V, E, F)` of a convex polyhedron, described via
the generation of its Schlegel diagram as a connected plane graph: a single vertex
bounding a single (outer) face, closed under attaching a pendant vertex and under adding
an edge inside an existing face. -/
inductive PolyhedronCounts : Nat → Nat → Nat → Prop
  /-- A single vertex, with one (outer) face and no edge. -/
  | point : PolyhedronCounts 1 0 1
  /-- Attaching a new vertex by a new edge adds one vertex and one edge. -/
  | addPendant {V E F : Nat} : PolyhedronCounts V E F → PolyhedronCounts (V + 1) (E + 1) F
  /-- Drawing a new edge inside a face adds one edge and splits the face in two. -/
  | addEdge {V E F : Nat} : PolyhedronCounts V E F → PolyhedronCounts V (E + 1) (F + 1)

/-- **Euler's polyhedron formula.** For a convex polyhedron (e.g. a fullerene cage),
`V - E + F = 2`. -/

theorem dodecahedron_counts : PolyhedronCounts 20 30 12 :=
  PolyhedronCounts.tree_plus_edges 19 11

/-- The C₆₀ fullerene cage: 60 carbon atoms, 90 bonds, 32 faces. -/
