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

/-- A combinatorial model of the surface of a convex polyhedron (e.g. a fullerene cage).

The data consist of the vertex set, the face set, the *skeleton* (the 1-skeleton graph of the
polyhedron, a simple graph since a convex polyhedron has no multiple edges), the *dual* graph on
the faces (also simple, since two facets of a convex polytope meet in at most one edge), and the
bijection `dualEdge` between the edges of the skeleton and the edges of the dual, coming from the
fact that every edge of a polyhedron is shared by exactly two faces.

Sphericity (planarity) of the surface is encoded by the classical *tree–cotree* structure: there
is a spanning tree `tree` of the skeleton whose complementary edges are exactly the edges of a
spanning tree `cotree` of the dual graph. Such an interdigitating pair of trees exists precisely
for maps on the sphere, and in particular for every convex polyhedron. -/
structure PolyhedralSurface where
  /-- The vertices of the polyhedron. -/
  Vertex : Type
  /-- The faces of the polyhedron. -/
  Face : Type
  [finiteVertex : Finite Vertex]
  [finiteFace : Finite Face]
  /-- The 1-skeleton: vertices and edges of the polyhedron. -/
  skeleton : SimpleGraph Vertex
  /-- The dual graph: faces are adjacent when they share an edge. -/
  dual : SimpleGraph Face
  /-- Each edge of the polyhedron is shared by exactly two faces; this is the resulting
  bijection between primal and dual edges. -/
  dualEdge : skeleton.edgeSet ≃ dual.edgeSet
  /-- A spanning tree of the skeleton. -/
  tree : SimpleGraph Vertex
  tree_le : tree ≤ skeleton
  tree_isTree : tree.IsTree
  /-- A spanning tree of the dual graph. -/
  cotree : SimpleGraph Face
  cotree_le : cotree ≤ dual
  cotree_isTree : cotree.IsTree
  /-- The two trees interdigitate: the dual edges of the non-tree edges are exactly the
  cotree edges. -/
  interdigitating : ∀ e : skeleton.edgeSet,
    (dualEdge e : Sym2 Face) ∈ cotree.edgeSet ↔ (e : Sym2 Vertex) ∉ tree.edgeSet

namespace PolyhedralSurface

instance (P : PolyhedralSurface) : Finite P.Vertex := P.finiteVertex
instance (P : PolyhedralSurface) : Finite P.Face := P.finiteFace

/-- The number of vertices. -/
noncomputable def numVertices (P : PolyhedralSurface) : ℕ := Nat.card P.Vertex

/-- The number of edges. -/
noncomputable def numEdges (P : PolyhedralSurface) : ℕ := Nat.card P.skeleton.edgeSet

/-- The number of faces. -/
noncomputable def numFaces (P : PolyhedralSurface) : ℕ := Nat.card P.Face

/-- Every edge is either a tree edge or (dually) a cotree edge, so the edges are counted by the
tree edges together with the cotree edges. -/
theorem numEdges_eq (P : PolyhedralSurface) :
    P.numEdges = Nat.card P.tree.edgeSet + Nat.card P.cotree.edgeSet := by
  classical
  set p : P.skeleton.edgeSet → Prop := fun e => (e : Sym2 P.Vertex) ∈ P.tree.edgeSet with hp
  have e1 : {e : P.skeleton.edgeSet // p e} ≃ P.tree.edgeSet :=
    Equiv.subtypeSubtypeEquivSubtype (fun {x} hx => edgeSet_mono P.tree_le hx)
  have e2 : {e : P.skeleton.edgeSet // ¬ p e} ≃
      {d : P.dual.edgeSet // (d : Sym2 P.Face) ∈ P.cotree.edgeSet} :=
    Equiv.subtypeEquiv P.dualEdge (fun e => (P.interdigitating e).symm)
  have e3 : {d : P.dual.edgeSet // (d : Sym2 P.Face) ∈ P.cotree.edgeSet} ≃ P.cotree.edgeSet :=
    Equiv.subtypeSubtypeEquivSubtype (fun {x} hx => edgeSet_mono P.cotree_le hx)
  have hsplit : Nat.card P.skeleton.edgeSet
      = Nat.card {e : P.skeleton.edgeSet // p e} + Nat.card {e : P.skeleton.edgeSet // ¬ p e} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl p).symm
  rw [numEdges, hsplit, Nat.card_congr e1, Nat.card_congr (e2.trans e3)]

end PolyhedralSurface

/-- **Euler's polyhedron formula**: for a convex polyhedron (for instance a fullerene cage),
`V - E + F = 2`.

The polyhedron is modelled combinatorially by `Chem.PolyhedralSurface`; sphericity is encoded by
the interdigitating pair of spanning trees of the skeleton and of the dual graph. The proof is the
tree–cotree argument: the spanning tree has `V - 1` edges and the dual spanning tree has `F - 1`
edges (`SimpleGraph.isTree_iff_connected_and_card`), and every edge is counted exactly once. -/
theorem euler_polyhedron (P : PolyhedralSurface) :
    (P.numVertices : ℤ) - P.numEdges + P.numFaces = 2 := by
  have hV : Nat.card P.tree.edgeSet + 1 = Nat.card P.Vertex :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.tree_isTree).2
  have hF : Nat.card P.cotree.edgeSet + 1 = Nat.card P.Face :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.cotree_isTree).2
  have hE := P.numEdges_eq
  simp only [PolyhedralSurface.numVertices, PolyhedralSurface.numFaces] at *
  omega

/-!
## Non-vacuity: the tetrahedron

The tetrahedron is a genuine instance of `PolyhedralSurface` (with `V = 4`, `E = 6`, `F = 4`),
so the hypotheses of `Chem.euler_polyhedron` are satisfiable.
-/

/-- The spanning tree `0 - 1 - 2 - 3` of the tetrahedron's skeleton `K₄`. -/
def tetTree : SimpleGraph (Fin 4) := fromEdgeSet {s(0, 1), s(1, 2), s(2, 3)}

instance : DecidableRel tetTree.Adj := fun u v => by
  unfold tetTree
  simp only [fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  infer_instance

theorem tetTree_eq_pathGraph : tetTree = pathGraph 4 := by
  ext u v
  simp only [tetTree, fromEdgeSet_adj, pathGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases u <;> fin_cases v <;> simp

theorem tetTree_isTree : tetTree.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨tetTree_eq_pathGraph ▸ pathGraph_connected 3, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- Being a tree edge, as a predicate on the edges of `K₄`. -/
abbrev tetIsTreeEdge : (⊤ : SimpleGraph (Fin 4)).edgeSet → Prop :=
  fun e => (e : Sym2 (Fin 4)) ∈ tetTree.edgeSet

/-- The three tree edges and the three non-tree edges of `K₄` are equinumerous. -/
noncomputable def tetTreeEquivCotree :
    {e // tetIsTreeEdge e} ≃ {e // ¬ tetIsTreeEdge e} := Fintype.equivOfCardEq (by decide)

/-- Identification of the edges of the tetrahedron with the edges of its dual (again a
tetrahedron), chosen so that the tree edges correspond to the non-tree edges. -/
noncomputable def tetDualEdge :
    (⊤ : SimpleGraph (Fin 4)).edgeSet ≃ (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  (Equiv.sumCompl tetIsTreeEdge).symm.trans
    ((tetTreeEquivCotree.sumCongr tetTreeEquivCotree.symm).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl tetIsTreeEdge)))

theorem tet_interdigitating (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    ((tetDualEdge e : Sym2 (Fin 4)) ∈ tetTree.edgeSet) ↔ (e : Sym2 (Fin 4)) ∉ tetTree.edgeSet := by
  by_cases h : tetIsTreeEdge e
  · rw [tetDualEdge]
    simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos h, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumComm_apply, Sum.swap_inl, Equiv.sumCompl_apply_inr, h,
      not_true_eq_false, iff_false]
    exact (tetTreeEquivCotree ⟨e, h⟩).2
  · rw [tetDualEdge]
    simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg h, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumComm_apply, Sum.swap_inr, Equiv.sumCompl_apply_inl, h,
      not_false_eq_true, iff_true]
    exact (tetTreeEquivCotree.symm ⟨e, h⟩).2

/-- The tetrahedron, as a polyhedral surface: skeleton and dual graph are both `K₄`. -/
noncomputable def tetrahedron : PolyhedralSurface where
  Vertex := Fin 4
  Face := Fin 4
  skeleton := ⊤
  dual := ⊤
  dualEdge := tetDualEdge
  tree := tetTree
  tree_le := le_top
  tree_isTree := tetTree_isTree
  cotree := tetTree
  cotree_le := le_top
  cotree_isTree := tetTree_isTree
  interdigitating := tet_interdigitating

theorem tetrahedron_counts :
    tetrahedron.numVertices = 4 ∧ tetrahedron.numEdges = 6 ∧ tetrahedron.numFaces = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PolyhedralSurface.numVertices, PolyhedralSurface.numEdges,
      PolyhedralSurface.numFaces, tetrahedron, Nat.card_eq_fintype_card] <;>
    decide

/-!
## A chemical consequence: every fullerene cage has exactly twelve pentagons
-/

/-- **Fullerene pentagon count.** A fullerene cage is a convex polyhedron whose faces are
pentagons (`p` of them) and hexagons (`h` of them) and in which every vertex has degree three.
Euler's formula forces `p = 12`, independently of the number of hexagons.

The hypotheses are the numerical consequences of the chemical description: `3 * V = 2 * E`
(each vertex lies on three edges, each edge has two ends), `F = p + h`, and `5 * p + 6 * h = 2 * E`
(each edge borders exactly two faces). -/
theorem fullerene_pentagon_count {V E F p h : ℕ}
    (hEuler : (V : ℤ) - E + F = 2)
    (hdeg : 3 * V = 2 * E)
    (hfaces : F = p + h)
    (hsizes : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-- The buckminsterfullerene cage C₆₀: twelve pentagons and twenty hexagons give
`V = 60`, `E = 90`, `F = 32`. -/
theorem c60_counts {V E F p h : ℕ} (hEuler : (V : ℤ) - E + F = 2) (hdeg : 3 * V = 2 * E)
    (hfaces : F = p + h) (hsizes : 5 * p + 6 * h = 2 * E) (hhex : h = 20) :
    V = 60 ∧ E = 90 ∧ F = 32 := by
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

