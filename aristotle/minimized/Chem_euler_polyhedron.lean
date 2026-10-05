/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/--
Combinatorial model of the plane graph obtained from a convex polyhedron
(for instance a fullerene cage) by a Schlegel projection: the vertices and edges of the
polyhedron are drawn in the plane, one distinguished face becoming the unbounded region,
so that the number of regions of the drawing equals the number of faces of the polyhedron.

`PlaneGraph V E F` says that a connected plane graph with `V` vertices, `E` edges and
`F` faces (regions, the unbounded one included) can be built up from a single point by
the two standard plane operations:

* attaching a new vertex along a new edge (this does not change the number of regions);
* drawing a new edge between two existing vertices (this splits one region into two).

Every connected plane graph arises in this way: build a spanning tree first, then draw
the remaining edges one by one.
-/
inductive PlaneGraph : Nat → Nat → Nat → Prop where
  /-- A single vertex, no edges, one (unbounded) region. -/
  | point : PlaneGraph 1 0 1
  /-- Attach a pendant vertex along a new edge: the number of regions is unchanged. -/
  | addVertex {V E F : Nat} : PlaneGraph V E F → PlaneGraph (V + 1) (E + 1) F
  /-- Draw a new edge between two existing vertices: one region is split in two. -/
  | addEdge {V E F : Nat} : PlaneGraph V E F → PlaneGraph V (E + 1) (F + 1)

/-- Euler's formula in the natural numbers: `V + F = E + 2`. -/

theorem euler_polyhedron_nat {V E F : Nat} (h : PlaneGraph V E F) : V + F = E + 2 := by
  induction h with
  | point => rfl
  | addVertex _ ih => omega
  | addEdge _ ih => omega

/--
**Euler's polyhedron formula.** For a convex polyhedron (e.g. a fullerene cage) with
`V` vertices, `E` edges and `F` faces, one has `V - E + F = 2`.
-/
