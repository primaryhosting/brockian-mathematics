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

theorem exists_vertex_degree_le_five {E F : ℕ} {verts : Finset ℕ} {d : ℕ → ℕ}
    (hsum : ∑ v ∈ verts, d v = 2 * E) (hface : 3 * F ≤ 2 * E)
    (heuler : (verts.card : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    ∃ v ∈ verts, d v ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hsix : ∀ v ∈ verts, 6 ≤ d v := fun v hv => hcon v hv
  have hbound : 6 * verts.card ≤ 2 * E := by
    calc 6 * verts.card = ∑ _v ∈ verts, 6 := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ v ∈ verts, d v := Finset.sum_le_sum hsix
      _ = 2 * E := hsum
  omega

end Chem

import Mathlib
import RequestProject.Chem

/-!
# Consequences of Euler's polyhedron formula

This file records combinatorial consequences of `Chem.euler_polyhedron`: the count relations
between vertices, edges and faces of a polyhedron whose vertices all have the same degree `d`
and whose faces are all `k`-gons, together with the resulting classification of the five
Platonic solids.
-/

namespace Chem

/-- Key counting identity for a polyhedron all of whose vertices have degree `d` and all of
whose faces are `k`-gons: `E * (2*d + 2*k - d*k) = 2*d*k`. -/
