import Mathlib
import RequestProject.Chem

/-!
# Polyhedral cages with full incidence data

The previous modules describe a polyhedral surface by its vertex, edge and face sets.  Here the
incidence structure itself is formalized: a `Cage` carries, besides the three finite sets, the
endpoint set of every edge and the boundary-edge set of every face.  Well-formedness (`Cage.WF`)
demands what a closed polyhedral surface must satisfy:

* every edge has exactly two endpoints, both of them vertices;
* every face is bounded by at least three edges of the surface;
* **every edge lies on exactly two faces** — the closed-surface condition.

The two basic construction steps (subdividing an edge, splitting a face by a diagonal) are
defined on the incidence data and are proved to preserve well-formedness, and Euler's formula
`|V| - |E| + |F| = 2` is proved for every cage built in this way.
-/

namespace Chem

open Finset

/-- A polyhedral cage: finite sets of vertices, edges and faces together with the incidence
data (endpoints of each edge, boundary edges of each face). -/
structure Cage where
  /-- The vertex set. -/
  V : Finset ℕ
  /-- The edge set. -/
  E : Finset ℕ
  /-- The face set. -/
  F : Finset ℕ
  /-- The two endpoints of an edge. -/
  ends : ℕ → Finset ℕ
  /-- The boundary edges of a face. -/
  sides : ℕ → Finset ℕ

/-- Well-formedness of a cage: edges have two endpoints among the vertices, faces are bounded
by at least three edges of the cage, and every edge lies on exactly two faces. -/

theorem buckyballCage_rings :
    (buckyballCage.F.filter fun f => (buckyballCage.sides f).card = 5).card = 12 ∧
      (buckyballCage.F.filter fun f => (buckyballCage.sides f).card = 6).card = 20 := by
  refine ⟨?_, ?_⟩ <;> decide

end Chem

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Combinatorial description of sphere-like polyhedra (closed convex polyhedral surfaces),
recorded through their vertex, edge and face counts.

`IsPolyhedron V E F` means: a polyhedral surface with `V` vertices, `E` edges and `F` faces
can be built from the tetrahedron by the standard construction steps

* subdividing an edge by a new vertex (`V+1, E+1, F`);
* joining two vertices of a face by a new diagonal edge (`V, E+1, F+1`);
* erecting a pyramid over a `k`-gonal face, `k ≥ 3` (`V+1, E+k, F+k-1`);
* truncating a vertex of degree `d`, `d ≥ 3` (`V+d-1, E+d, F+1`).

All of these operations preserve the topological type of the surface (a sphere). -/
inductive IsPolyhedron : Nat → Nat → Nat → Prop
  /-- The tetrahedron: 4 vertices, 6 edges, 4 faces. -/
  | tetrahedron : IsPolyhedron 4 6 4
  /-- Subdivide an edge by inserting a new vertex in its interior. -/
  | subdivideEdge {V E F : Nat} : IsPolyhedron V E F → IsPolyhedron (V + 1) (E + 1) F
  /-- Split a face into two by drawing a diagonal. -/
  | splitFace {V E F : Nat} : IsPolyhedron V E F → IsPolyhedron V (E + 1) (F + 1)
  /-- Erect a pyramid over a `k`-gonal face (`k ≥ 3`). -/
  | pyramid {V E F : Nat} (k : Nat) (hk : 3 ≤ k) :
      IsPolyhedron V E F → IsPolyhedron (V + 1) (E + k) (F + (k - 1))
  /-- Truncate (cut off) a vertex of degree `d` (`d ≥ 3`). -/
  | truncate {V E F : Nat} (d : Nat) (hd : 3 ≤ d) :
      IsPolyhedron V E F → IsPolyhedron (V + (d - 1)) (E + d) (F + 1)

/-- **Euler's polyhedron formula.** For a convex polyhedron (for instance a fullerene cage)
with `V` vertices, `E` edges and `F` faces one has `V - E + F = 2`. -/
