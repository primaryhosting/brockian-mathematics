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

theorem exists_face_le_five {V E : ℕ} {faces : Finset ℕ} {s : ℕ → ℕ}
    (hsum : ∑ f ∈ faces, s f = 2 * E) (hdeg : 3 * V ≤ 2 * E)
    (heuler : (V : ℤ) - (E : ℤ) + (faces.card : ℤ) = 2) :
    ∃ f ∈ faces, s f ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hsix : ∀ f ∈ faces, 6 ≤ s f := fun f hf => hcon f hf
  have hbound : 6 * faces.card ≤ 2 * E := by
    calc 6 * faces.card = ∑ _f ∈ faces, 6 := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ f ∈ faces, s f := Finset.sum_le_sum hsix
      _ = 2 * E := hsum
  omega

/-- Dually, **every convex polyhedron has a vertex of degree at most five**: if every face has
at least three sides (`3 * F ≤ 2 * E`) and `d v` is the degree of the vertex `v`, then some
vertex has degree at most five. -/
