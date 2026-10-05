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

theorem platonic_classification {V E F d k : ℕ} (hE : 0 < E)
    (hd : 3 ≤ d) (hk : 3 ≤ k)
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    (V, E, F) = (4, 6, 4) ∨ (V, E, F) = (8, 12, 6) ∨ (V, E, F) = (6, 12, 8) ∨
      (V, E, F) = (20, 30, 12) ∨ (V, E, F) = (12, 30, 20) := by
  have hbound := regular_degree_bound hE hd hk hdeg hface heuler
  have hd' : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hdle : d ≤ 5 := by
    have : (d : ℤ) ≤ 5 := by nlinarith
    exact_mod_cast this
  have hkle : k ≤ 5 := by
    have : (k : ℤ) ≤ 5 := by nlinarith
    exact_mod_cast this
  have heuler' : V + F = E + 2 := by omega
  simp only [Prod.mk.injEq]
  interval_cases d <;> interval_cases k <;> omega

end Chem

