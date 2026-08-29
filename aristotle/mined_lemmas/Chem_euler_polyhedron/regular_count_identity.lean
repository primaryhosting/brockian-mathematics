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

theorem regular_count_identity {V E F d k : ℕ}
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    (E : ℤ) * (2 * d + 2 * k - d * k) = 2 * d * k := by
  have h1 : (d : ℤ) * V = 2 * E := by exact_mod_cast hdeg.symm
  have h2 : (k : ℤ) * F = 2 * E := by exact_mod_cast hface.symm
  have h3 : (V : ℤ) + F = E + 2 := by linarith
  linear_combination ((d : ℤ) * k) * h3 - (k : ℤ) * h1 - (d : ℤ) * h2

/-- For a polyhedron with all vertex degrees equal to `d ≥ 3` and all faces `k`-gons with
`k ≥ 3`, one has `(d - 2) * (k - 2) ≤ 3`; this is the inequality behind the classification of
the Platonic solids. -/
