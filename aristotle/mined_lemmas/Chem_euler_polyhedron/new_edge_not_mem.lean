/-
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

/-- Combinatorial data of a graph drawn on the sphere (equivalently, of the
surface of a polyhedron): a finite set of vertices, a finite set of edges
(unordered pairs of vertices), and the number of faces of the drawing. -/
structure PlaneGraph where
  /-- The vertices of the drawing. -/
  verts : Finset ℕ
  /-- The edges of the drawing, as unordered pairs of vertices. -/
  edges : Finset (Sym2 ℕ)
  /-- The number of faces (regions) that the drawing cuts the sphere into. -/
  faces : ℕ

/-- Connected drawings on the sphere, described by the two elementary
construction steps that build every polyhedral surface starting from a single
vertex (whose complement on the sphere is a single face):

* `addVertex`: draw a new vertex `w` together with an edge joining it to an
  already drawn vertex `u`.  This creates no new region, so the face count is
  unchanged.
* `addEdge`: draw a new edge between two vertices that are already present.
  Since the drawing is connected, such an edge cuts an existing region in two,
  so the face count grows by one.

Every convex polyhedron (in particular every fullerene cage) has its
vertex–edge–face incidence structure produced this way: draw a spanning tree of
the polyhedron's skeleton with `base`/`addVertex`, then insert the remaining
edges with `addEdge`. -/
inductive Builds : PlaneGraph → Prop
  | base (v : ℕ) : Builds ⟨{v}, ∅, 1⟩
  | addVertex {G : PlaneGraph} (h : Builds G) (u w : ℕ)
      (hu : u ∈ G.verts) (hw : w ∉ G.verts) :
      Builds ⟨insert w G.verts, insert s(u, w) G.edges, G.faces⟩
  | addEdge {G : PlaneGraph} (h : Builds G) (u w : ℕ)
      (hu : u ∈ G.verts) (hw : w ∈ G.verts) (hnew : s(u, w) ∉ G.edges) :
      Builds ⟨G.verts, insert s(u, w) G.edges, G.faces + 1⟩

/-- Every endpoint of every edge of a drawn graph is a drawn vertex. -/

theorem new_edge_not_mem {G : PlaneGraph} (h : Builds G) {u w : ℕ}
    (hw : w ∉ G.verts) : s(u, w) ∉ G.edges := by
  intro hmem
  exact hw (mem_verts_of_mem_edge h _ hmem w (Sym2.mem_mk_right u w))

/-- **Euler's polyhedron formula**, natural-number form: for a connected graph
drawn on the sphere — e.g. the skeleton of a convex polyhedron such as a
fullerene cage — the number of vertices plus the number of faces equals the
number of edges plus two. -/
