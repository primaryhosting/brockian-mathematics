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
theorem mem_verts_of_mem_edge {G : PlaneGraph} (h : Builds G) :
    ∀ e ∈ G.edges, ∀ x ∈ e, x ∈ G.verts := by
  induction h with
  | base v => simp
  | addVertex h u w hu hw ih =>
      intro e he x hx
      simp only [Finset.mem_insert] at he ⊢
      rcases he with rfl | he
      · rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact Or.inr hu
        · exact Or.inl rfl
      · exact Or.inr (ih e he x hx)
  | addEdge h u w hu hw hnew ih =>
      intro e he x hx
      simp only [Finset.mem_insert] at he
      rcases he with rfl | he
      · rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hu
        · exact hw
      · exact ih e he x hx

/-- The two ends of a newly drawn vertex's edge cannot already be an edge. -/
theorem new_edge_not_mem {G : PlaneGraph} (h : Builds G) {u w : ℕ}
    (hw : w ∉ G.verts) : s(u, w) ∉ G.edges := by
  intro hmem
  exact hw (mem_verts_of_mem_edge h _ hmem w (Sym2.mem_mk_right u w))

/-- **Euler's polyhedron formula**, natural-number form: for a connected graph
drawn on the sphere — e.g. the skeleton of a convex polyhedron such as a
fullerene cage — the number of vertices plus the number of faces equals the
number of edges plus two. -/
theorem euler_polyhedron_nat {G : PlaneGraph} (h : Builds G) :
    G.verts.card + G.faces = G.edges.card + 2 := by
  induction h with
  | base v => simp
  | addVertex h u w hu hw ih =>
      have hedge := new_edge_not_mem (u := u) h hw
      simp only [Finset.card_insert_of_notMem hw, Finset.card_insert_of_notMem hedge]
      omega
  | addEdge h u w hu hw hnew ih =>
      simp only [Finset.card_insert_of_notMem hnew]
      omega

/-- **Euler's polyhedron formula**: for a convex polyhedron (e.g. a fullerene
cage), with `V` vertices, `E` edges and `F` faces, one has `V - E + F = 2`. -/
theorem euler_polyhedron {G : PlaneGraph} (h : Builds G) :
    (G.verts.card : ℤ) - (G.edges.card : ℤ) + (G.faces : ℤ) = 2 := by
  have := euler_polyhedron_nat h
  omega

/-- **Fullerene cages.**  A fullerene such as C₆₀ has 60 carbon atoms
(vertices) and 90 bonds (edges); Euler's formula forces its cage to have
exactly 32 faces (the familiar 12 pentagons and 20 hexagons). -/
theorem fullerene_faces {G : PlaneGraph} (h : Builds G)
    (hV : G.verts.card = 60) (hE : G.edges.card = 90) : G.faces = 32 := by
  have := euler_polyhedron_nat h
  omega

/-- The tetrahedron (the complete graph on four vertices, drawn on the sphere)
is a polyhedral drawing: it has 4 vertices, 6 edges and 4 faces. -/
theorem builds_tetrahedron :
    Builds ⟨{0, 1, 2, 3},
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)}, 4⟩ := by
  have h0 : Builds ⟨{0}, ∅, 1⟩ := Builds.base 0
  have h1 := h0.addVertex 0 1 (by decide) (by decide)
  have h2 := h1.addVertex 0 2 (by decide) (by decide)
  have h3 := h2.addVertex 0 3 (by decide) (by decide)
  have h4 := h3.addEdge 1 2 (by decide) (by decide) (by decide)
  have h5 := h4.addEdge 1 3 (by decide) (by decide) (by decide)
  have h6 := h5.addEdge 2 3 (by decide) (by decide) (by decide)
  convert h6 using 2 <;> decide

/-- Euler's formula, read off on the tetrahedron: `V - E + F = 4 - 6 + 4 = 2`. -/
example :
    ((({0, 1, 2, 3} : Finset ℕ).card : ℤ)
      - (({s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)} :
          Finset (Sym2 ℕ)).card : ℤ) + (4 : ℤ) = 2) :=
  euler_polyhedron builds_tetrahedron

end Chem

