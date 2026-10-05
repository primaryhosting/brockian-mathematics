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
theorem euler_polyhedron {V E F : Nat} (h : PolyhedronCounts V E F) :
    (V : Int) - (E : Int) + (F : Int) = 2 := by
  induction h with
  | point => omega
  | addPendant _ ih => omega
  | addEdge _ ih => omega

/-- Non-vacuity: a spanning tree on `n + 1` vertices together with `k` further edges is an
admissible plane graph, and it has `k + 1` faces. -/
theorem PolyhedronCounts.tree_plus_edges (n k : Nat) :
    PolyhedronCounts (n + 1) (n + k) (k + 1) := by
  induction k with
  | zero =>
      induction n with
      | zero => exact PolyhedronCounts.point
      | succ m ih => exact ih.addPendant
  | succ j ih =>
      have h := ih.addEdge
      have hn : n + j + 1 = n + (j + 1) := by omega
      rwa [hn] at h

/-- The tetrahedron: 4 vertices, 6 edges, 4 faces. -/
theorem tetrahedron_counts : PolyhedronCounts 4 6 4 :=
  PolyhedronCounts.tree_plus_edges 3 3

/-- The cube: 8 vertices, 12 edges, 6 faces. -/
theorem cube_counts : PolyhedronCounts 8 12 6 :=
  PolyhedronCounts.tree_plus_edges 7 5

/-- The dodecahedron: 20 vertices, 30 edges, 12 faces. -/
theorem dodecahedron_counts : PolyhedronCounts 20 30 12 :=
  PolyhedronCounts.tree_plus_edges 19 11

/-- The C₆₀ fullerene cage: 60 carbon atoms, 90 bonds, 32 faces. -/
theorem c60_counts : PolyhedronCounts 60 90 32 :=
  PolyhedronCounts.tree_plus_edges 59 31

/-- Euler's formula for the C₆₀ fullerene cage: `60 - 90 + 32 = 2`. -/
theorem c60_euler : (60 : Int) - 90 + 32 = 2 := euler_polyhedron c60_counts

/-- **Every fullerene cage has exactly twelve pentagonal faces.**
From Euler's formula, three-valence of every carbon atom (`3 * V = 2 * E`) and the fact
that each of the `F` faces is a pentagon (`p` of them) or a hexagon (`h` of them), so that
`5 * p + 6 * h = 2 * E`, one gets `p = 12`. -/
theorem fullerene_twelve_pentagons {V E F p h : Int}
    (hEuler : V - E + F = 2) (hDeg : 3 * V = 2 * E) (hFaces : F = p + h)
    (hEdges : 5 * p + 6 * h = 2 * E) : p = 12 := by
  omega

end Chem

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

