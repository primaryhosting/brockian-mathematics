/-
/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Combinatorial model

We model the (boundary) surface of a convex polyhedron -- for instance a fullerene cage --
by its combinatorial incidence data together with a *tree-cotree* (interdigitating spanning
trees) decomposition of its edge set, which is the combinatorial expression of the fact that
the surface is a sphere.

Explicitly, a `PolyhedralSurface` consists of finite sets of vertices, edges and faces,
where each edge has two distinct endpoints and two distinct incident faces, and a
distinguished set `tree` of edges such that

* the edges of `tree` form a spanning tree of the vertex-edge graph (the 1-skeleton), and
* the remaining edges form a spanning tree of the dual graph on faces.

Every convex polyhedron has such a decomposition: take any spanning tree `T` of its
1-skeleton; the dual edges corresponding to the edges outside `T` then form a spanning tree
of the dual graph.

Euler's formula `V - E + F = 2` is proved from this data, and, as a chemical corollary,
that a trivalent cage all of whose faces are pentagons or hexagons has exactly 12
pentagonal faces (as in a fullerene).
-/

namespace Chem

open Finset

/-- Combinatorial data describing the surface of a convex polyhedron (e.g. a fullerene cage):
vertices, edges and faces, the two endpoints and two incident faces of each edge, and a
tree-cotree decomposition of the edge set witnessing that the surface is a sphere. -/
structure PolyhedralSurface where
  /-- The set of vertices. -/
  Vert : Type
  /-- The set of edges. -/
  Edge : Type
  /-- The set of faces. -/
  Face : Type
  [finVert : Fintype Vert]
  [finEdge : Fintype Edge]
  [finFace : Fintype Face]
  [decVert : DecidableEq Vert]
  [decEdge : DecidableEq Edge]
  [decFace : DecidableEq Face]
  /-- The (unordered) pair of endpoints of an edge. -/
  ends : Edge → Sym2 Vert
  /-- The (unordered) pair of faces incident with an edge. -/
  sides : Edge → Sym2 Face
  /-- The two endpoints of an edge are distinct. -/
  ends_not_isDiag : ∀ e, ¬ (ends e).IsDiag
  /-- The two faces incident with an edge are distinct. -/
  sides_not_isDiag : ∀ e, ¬ (sides e).IsDiag
  /-- The edges of a distinguished spanning tree of the 1-skeleton. -/
  tree : Finset Edge
  /-- The spanning tree of the 1-skeleton. -/
  primalTree : SimpleGraph Vert
  /-- The spanning tree of the dual graph. -/
  dualTree : SimpleGraph Face
  [finPrimal : Fintype primalTree.edgeSet]
  [finDual : Fintype dualTree.edgeSet]
  primalTree_isTree : primalTree.IsTree
  dualTree_isTree : dualTree.IsTree
  /-- The edges of `primalTree` are exactly the edges in `tree`. -/
  primal_edgeFinset : primalTree.edgeFinset = tree.image ends
  /-- The edges of `dualTree` are exactly the duals of the edges outside `tree`. -/
  dual_edgeFinset : dualTree.edgeFinset = treeᶜ.image sides
  /-- Distinct tree edges have distinct endpoint pairs. -/
  ends_injOn : Set.InjOn ends tree
  /-- Distinct cotree edges have distinct incident face pairs. -/
  sides_injOn : Set.InjOn sides (↑treeᶜ)

attribute [instance] PolyhedralSurface.finVert PolyhedralSurface.finEdge
  PolyhedralSurface.finFace PolyhedralSurface.decVert PolyhedralSurface.decEdge
  PolyhedralSurface.decFace PolyhedralSurface.finPrimal PolyhedralSurface.finDual

namespace PolyhedralSurface

variable (P : PolyhedralSurface)

/-- The number of vertices `V`. -/
def numVertices : ℕ := Fintype.card P.Vert

/-- The number of edges `E`. -/
def numEdges : ℕ := Fintype.card P.Edge

/-- The number of faces `F`. -/
def numFaces : ℕ := Fintype.card P.Face

/-- The spanning tree of the 1-skeleton has `V - 1` edges. -/
lemma card_tree : P.tree.card + 1 = P.numVertices := by
  have h : P.primalTree.edgeFinset.card = P.tree.card := by
    rw [P.primal_edgeFinset, Finset.card_image_of_injOn P.ends_injOn]
  rw [← h]
  exact P.primalTree_isTree.card_edgeFinset

/-- The spanning tree of the dual graph has `F - 1` edges. -/
lemma card_cotree : P.treeᶜ.card + 1 = P.numFaces := by
  have h : P.dualTree.edgeFinset.card = P.treeᶜ.card := by
    rw [P.dual_edgeFinset, Finset.card_image_of_injOn P.sides_injOn]
  rw [← h]
  exact P.dualTree_isTree.card_edgeFinset

end PolyhedralSurface

/-- **Euler's polyhedron formula.**  For (the combinatorial surface of) a convex polyhedron,
such as a fullerene cage, the numbers of vertices, edges and faces satisfy `V - E + F = 2`. -/
theorem euler_polyhedron (P : PolyhedralSurface) :
    (P.numVertices : ℤ) - P.numEdges + P.numFaces = 2 := by
  have hV := P.card_tree
  have hF := P.card_cotree
  have hE : P.tree.card + P.treeᶜ.card = P.numEdges :=
    Finset.card_add_card_compl P.tree
  omega

/-!
## A chemical corollary: fullerenes have exactly 12 pentagons
-/

namespace PolyhedralSurface

variable (P : PolyhedralSurface)

/-- The degree of a vertex: the number of edges incident with it. -/
def degree (v : P.Vert) : ℕ := (univ.filter fun e => v ∈ P.ends e).card

/-- The size of a face: the number of edges incident with it. -/
def faceSize (f : P.Face) : ℕ := (univ.filter fun e => f ∈ P.sides e).card

private lemma card_filter_mem_sym2 {α : Type} [Fintype α] [DecidableEq α] (s : Sym2 α)
    (h : ¬ s.IsDiag) : (univ.filter fun v => v ∈ s).card = 2 := by
  induction s with
  | _ a b =>
    have hab : a ≠ b := by simpa using h
    have hs : (univ.filter fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp
    rw [hs, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

/-- Handshake lemma for the 1-skeleton: the degrees of the vertices sum to twice the
number of edges. -/
lemma sum_degree : ∑ v, P.degree v = 2 * P.numEdges := by
  classical
  have : ∑ v : P.Vert, P.degree v
      = ∑ e : P.Edge, (univ.filter fun v => v ∈ P.ends e).card := by
    simp only [degree, Finset.card_filter]
    exact Finset.sum_comm
  rw [this]
  have h2 : ∀ e : P.Edge, (univ.filter fun v => v ∈ P.ends e).card = 2 := fun e =>
    card_filter_mem_sym2 _ (P.ends_not_isDiag e)
  simp [h2, numEdges, mul_comm]

/-- Handshake lemma for the dual graph: the face sizes sum to twice the number of edges. -/
lemma sum_faceSize : ∑ f, P.faceSize f = 2 * P.numEdges := by
  classical
  have : ∑ f : P.Face, P.faceSize f
      = ∑ e : P.Edge, (univ.filter fun f => f ∈ P.sides e).card := by
    simp only [faceSize, Finset.card_filter]
    exact Finset.sum_comm
  rw [this]
  have h2 : ∀ e : P.Edge, (univ.filter fun f => f ∈ P.sides e).card = 2 := fun e =>
    card_filter_mem_sym2 _ (P.sides_not_isDiag e)
  simp [h2, numEdges, mul_comm]

end PolyhedralSurface

/-- **Fullerenes have exactly twelve pentagonal faces.**  If every vertex of a polyhedral
surface has degree three and every face is a pentagon or a hexagon, then exactly twelve of
the faces are pentagons. -/
theorem fullerene_pentagon_count (P : PolyhedralSurface)
    (hdeg : ∀ v, P.degree v = 3)
    (hface : ∀ f, P.faceSize f = 5 ∨ P.faceSize f = 6) :
    (univ.filter fun f => P.faceSize f = 5).card = 12 := by
  classical
  set p := (univ.filter fun f => P.faceSize f = 5).card with hp
  set h := (univ.filter fun f => ¬ P.faceSize f = 5).card with hh
  have hEuler := euler_polyhedron P
  have hdegsum : 3 * P.numVertices = 2 * P.numEdges := by
    have := P.sum_degree
    rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at this
    simpa [PolyhedralSurface.numVertices, mul_comm] using this
  have hpF : p + h = P.numFaces := by
    rw [hp, hh]
    simpa [PolyhedralSurface.numFaces] using
      Finset.card_filter_add_card_filter_not
        (s := (univ : Finset P.Face)) (p := fun f => P.faceSize f = 5)
  have hfacesum : 5 * p + 6 * h = 2 * P.numEdges := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (univ : Finset P.Face) (fun f => P.faceSize f = 5) P.faceSize
    have h5 : ∑ f ∈ univ.filter (fun f => P.faceSize f = 5), P.faceSize f = 5 * p := by
      rw [Finset.sum_congr rfl (fun f hf => (Finset.mem_filter.mp hf).2)]
      simp [hp, mul_comm]
    have h6 : ∑ f ∈ univ.filter (fun f => ¬ P.faceSize f = 5), P.faceSize f = 6 * h := by
      have hall : ∀ f ∈ univ.filter (fun f => ¬ P.faceSize f = 5), P.faceSize f = 6 := by
        intro f hf
        rcases hface f with h5' | h6'
        · exact absurd h5' (Finset.mem_filter.mp hf).2
        · exact h6'
      rw [Finset.sum_congr rfl hall]
      simp [hh, mul_comm]
    rw [h5, h6] at hsplit
    rw [hsplit, P.sum_faceSize]
  omega


/-!
## The model is non-vacuous: the tetrahedron

To confirm that `PolyhedralSurface` really describes convex polyhedra, we exhibit the
tetrahedron: 4 vertices, 6 edges, 4 triangular faces.  Its 1-skeleton is `K₄`; we take as
spanning tree the star at vertex `0` (edges `{0,1}, {0,2}, {0,3}`), and the three remaining
edges are dual to the star at face `0` of the dual graph (which is again `K₄`).
-/

private lemma star4_isTree :
    (SimpleGraph.fromRel (fun a b : Fin 4 => a = 0 ∧ b ≠ 0)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨by decide, ?_⟩
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  decide

/-- The tetrahedron as a polyhedral surface. -/
def tetrahedron : PolyhedralSurface where
  Vert := Fin 4
  Edge := Fin 6
  Face := Fin 4
  ends := ![s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)]
  sides := ![s(2, 3), s(1, 3), s(1, 2), s(0, 3), s(0, 2), s(0, 1)]
  ends_not_isDiag := by decide
  sides_not_isDiag := by decide
  tree := {0, 1, 2}
  primalTree := SimpleGraph.fromRel (fun a b : Fin 4 => a = 0 ∧ b ≠ 0)
  dualTree := SimpleGraph.fromRel (fun a b : Fin 4 => a = 0 ∧ b ≠ 0)
  primalTree_isTree := star4_isTree
  dualTree_isTree := star4_isTree
  primal_edgeFinset := by decide
  dual_edgeFinset := by decide
  ends_injOn := by decide
  sides_injOn := by decide

example : tetrahedron.numVertices = 4 := by decide
example : tetrahedron.numEdges = 6 := by decide
example : tetrahedron.numFaces = 4 := by decide

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

