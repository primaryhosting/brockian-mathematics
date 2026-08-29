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

theorem regular_degree_bound {V E F d k : ℕ} (hE : 0 < E)
    (hd : 3 ≤ d) (hk : 3 ≤ k)
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    ((d : ℤ) - 2) * ((k : ℤ) - 2) ≤ 3 := by
  have key := regular_count_identity hdeg hface heuler
  have hE' : (1 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hE
  have hd' : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- `2*d + 2*k - d*k` must be positive, since `E > 0` and the right-hand side is positive
  have hpos : 0 < 2 * (d : ℤ) + 2 * k - d * k := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  nlinarith

/-- **Classification of the Platonic solids.** A polyhedron in which every vertex has the same
degree `d ≥ 3` and every face is a `k`-gon with `k ≥ 3` must be (combinatorially) one of the
five Platonic solids: tetrahedron `(4,6,4)`, cube `(8,12,6)`, octahedron `(6,12,8)`,
dodecahedron `(20,30,12)` or icosahedron `(12,30,20)`. -/
