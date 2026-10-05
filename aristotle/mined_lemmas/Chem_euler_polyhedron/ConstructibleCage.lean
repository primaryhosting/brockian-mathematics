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

theorem ConstructibleCage.isPolyhedron {C : Cage} (h : ConstructibleCage C) :
    IsPolyhedron C.V.card C.E.card C.F.card := by
  induction h with
  | tetra =>
      have hV : tetraCage.V.card = 4 := by decide
      have hE : tetraCage.E.card = 6 := by decide
      have hF : tetraCage.F.card = 4 := by decide
      rw [hV, hE, hF]
      exact IsPolyhedron.tetrahedron
  | @subdivide C e enew v b he hb hv hnew _ ih =>
      have hV : (C.subdivide e enew v b).V.card = C.V.card + 1 := by
        rw [Cage.subdivide_V, Finset.card_insert_of_notMem hv]
      have hE : (C.subdivide e enew v b).E.card = C.E.card + 1 := by
        rw [Cage.subdivide_E, Finset.card_insert_of_notMem hnew]
      have hF : (C.subdivide e enew v b).F.card = C.F.card := by rw [Cage.subdivide_F]
      rw [hV, hE, hF]
      exact IsPolyhedron.subdivideEdge ih
  | @splitFace C f fnew enew a b A hf hfnew hnew ha hb hab hA hAcard hBcard _ ih =>
      have hV : (C.splitFace f fnew enew a b A).V.card = C.V.card := by rw [Cage.splitFace_V]
      have hE : (C.splitFace f fnew enew a b A).E.card = C.E.card + 1 := by
        rw [Cage.splitFace_E, Finset.card_insert_of_notMem hnew]
      have hF : (C.splitFace f fnew enew a b A).F.card = C.F.card + 1 := by
        rw [Cage.splitFace_F, Finset.card_insert_of_notMem hfnew]
      rw [hV, hE, hF]
      exact IsPolyhedron.splitFace ih

/-- **Euler's polyhedron formula for cages with full incidence data.**  Every closed surface
built from the tetrahedron by subdividing edges and splitting faces satisfies
`|V| - |E| + |F| = 2`. -/
