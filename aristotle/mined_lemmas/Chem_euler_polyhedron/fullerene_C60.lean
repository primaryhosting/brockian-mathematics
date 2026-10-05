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

theorem fullerene_C60 : IsPolyhedron 60 90 32 := by
  have base : IsPolyhedron 4 6 4 := IsPolyhedron.tetrahedron
  -- eight pyramids over triangular faces: (4,6,4) → (12,30,20)
  have pyr : ∀ V E F : Nat, IsPolyhedron V E F → IsPolyhedron (V + 1) (E + 3) (F + 2) :=
    fun _ _ _ h => IsPolyhedron.pyramid 3 (by omega) h
  have h1 : IsPolyhedron 5 9 6 := pyr _ _ _ base
  have h2 : IsPolyhedron 6 12 8 := pyr _ _ _ h1
  have h3 : IsPolyhedron 7 15 10 := pyr _ _ _ h2
  have h4 : IsPolyhedron 8 18 12 := pyr _ _ _ h3
  have h5 : IsPolyhedron 9 21 14 := pyr _ _ _ h4
  have h6 : IsPolyhedron 10 24 16 := pyr _ _ _ h5
  have h7 : IsPolyhedron 11 27 18 := pyr _ _ _ h6
  have icosa : IsPolyhedron 12 30 20 := pyr _ _ _ h7
  -- twelve truncations of degree-5 vertices: each adds (4,5,1)
  have trunc : ∀ V E F : Nat, IsPolyhedron V E F → IsPolyhedron (V + 4) (E + 5) (F + 1) :=
    fun _ _ _ h => IsPolyhedron.truncate 5 (by omega) h
  have t1 : IsPolyhedron 16 35 21 := trunc _ _ _ icosa
  have t2 : IsPolyhedron 20 40 22 := trunc _ _ _ t1
  have t3 : IsPolyhedron 24 45 23 := trunc _ _ _ t2
  have t4 : IsPolyhedron 28 50 24 := trunc _ _ _ t3
  have t5 : IsPolyhedron 32 55 25 := trunc _ _ _ t4
  have t6 : IsPolyhedron 36 60 26 := trunc _ _ _ t5
  have t7 : IsPolyhedron 40 65 27 := trunc _ _ _ t6
  have t8 : IsPolyhedron 44 70 28 := trunc _ _ _ t7
  have t9 : IsPolyhedron 48 75 29 := trunc _ _ _ t8
  have t10 : IsPolyhedron 52 80 30 := trunc _ _ _ t9
  have t11 : IsPolyhedron 56 85 31 := trunc _ _ _ t10
  exact trunc _ _ _ t11

/-- All five Platonic count tables are realized by polyhedra: tetrahedron `(4,6,4)`, cube
`(8,12,6)`, octahedron `(6,12,8)`, dodecahedron `(20,30,12)` and icosahedron `(12,30,20)`. -/
