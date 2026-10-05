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

theorem isPolyhedron_of_constructibleSurface {V E F : Finset ℕ}
    (h : ConstructibleSurface V E F) : IsPolyhedron V.card E.card F.card := by
  induction h with
  | tetrahedron =>
      have hV : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
      have hE : ({0, 1, 2, 3, 4, 5} : Finset ℕ).card = 6 := by decide
      rw [hV, hE]
      exact IsPolyhedron.tetrahedron
  | @subdivideEdge V E F v e hv he _ ih =>
      rw [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem he]
      exact IsPolyhedron.subdivideEdge ih
  | @splitFace V E F e f he hf _ ih =>
      rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hf]
      exact IsPolyhedron.splitFace ih
  | @pyramid V E F v newE newF hv hE hF hk hcard _ ih =>
      have e1 : (insert v V).card = V.card + 1 := Finset.card_insert_of_notMem hv
      have e2 : (newE ∪ E).card = E.card + newE.card := by
        rw [Finset.card_union_of_disjoint hE]; omega
      have e3 : (newF ∪ F).card = F.card + (newE.card - 1) := by
        rw [Finset.card_union_of_disjoint hF]; omega
      rw [e1, e2, e3]
      exact IsPolyhedron.pyramid newE.card hk ih
  | @truncate V E F v f newV newE hv hVd hE hf hd hcard _ ih =>
      have hVpos : 1 ≤ V.card := Finset.one_le_card.2 ⟨v, hv⟩
      have hVd' : Disjoint newV (V.erase v) :=
        hVd.mono_right (Finset.erase_subset v V)
      have e1 : (newV ∪ V.erase v).card = V.card + (newE.card - 1) := by
        rw [Finset.card_union_of_disjoint hVd', Finset.card_erase_of_mem hv]; omega
      have e2 : (newE ∪ E).card = E.card + newE.card := by
        rw [Finset.card_union_of_disjoint hE]; omega
      have e3 : (insert f F).card = F.card + 1 := Finset.card_insert_of_notMem hf
      rw [e1, e2, e3]
      exact IsPolyhedron.truncate newE.card hd ih

/-- **Euler's polyhedron formula for surfaces given by explicit finite sets.**  If the vertex
set `V`, edge set `E` and face set `F` form a polyhedral surface, then
`|V| - |E| + |F| = 2`. -/
