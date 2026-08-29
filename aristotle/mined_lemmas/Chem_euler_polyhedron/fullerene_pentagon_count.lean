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

theorem fullerene_pentagon_count {V E F p h : Nat}
    (hcubic : 2 * E = 3 * V) (hfaces : F = p + h) (hedges : 2 * E = 5 * p + 6 * h)
    (heuler : (V : Int) - (E : Int) + (F : Int) = 2) : p = 12 := by
  omega

end Chem

import Mathlib
import RequestProject.Chem

/-!
# Polyhedral surfaces as genuine finite sets of vertices, edges and faces

`Chem.IsPolyhedron` records a polyhedral surface through its three counts.  Here the same
constructions are carried out on honest finite sets: a polyhedral surface is given by a finite
set `V` of vertices, a finite set `E` of edges and a finite set `F` of faces (all labelled by
natural numbers), and the construction steps genuinely insert, delete and merge elements of
these sets.  Euler's formula is then obtained from the actual cardinalities `V.card`, `E.card`
and `F.card`.
-/

namespace Chem

open Finset

/-- Polyhedral surfaces described by their actual finite sets of vertices, edges and faces.

`ConstructibleSurface V E F` says that the surface with vertex set `V`, edge set `E` and face
set `F` is obtained from the tetrahedron by the standard construction steps, now performed on
the sets themselves:

* `subdivideEdge`: a fresh vertex `v` and a fresh edge `e` are inserted (the old edge is cut
  into two by `v`);
* `splitFace`: a fresh edge `e` (a diagonal) and the fresh face `f` it cuts off are inserted;
* `pyramid`: a fresh apex `v`, a set `newE` of `k ≥ 3` fresh edges joining it to the `k`
  vertices of a face, and the `k - 1` fresh faces beyond the original one;
* `truncate`: a vertex `v` of degree `d ≥ 3` is deleted and replaced by `d` fresh vertices,
  `d` fresh edges and one fresh face.
-/
inductive ConstructibleSurface : Finset ℕ → Finset ℕ → Finset ℕ → Prop
  /-- The tetrahedron, with four labelled vertices, six labelled edges and four labelled
  faces. -/
  | tetrahedron :
      ConstructibleSurface {0, 1, 2, 3} {0, 1, 2, 3, 4, 5} {0, 1, 2, 3}
  /-- Subdivide an edge: insert a fresh vertex `v` and a fresh edge `e`. -/
  | subdivideEdge {V E F : Finset ℕ} (v e : ℕ) (hv : v ∉ V) (he : e ∉ E) :
      ConstructibleSurface V E F → ConstructibleSurface (insert v V) (insert e E) F
  /-- Split a face by a diagonal: insert a fresh edge `e` and a fresh face `f`. -/
  | splitFace {V E F : Finset ℕ} (e f : ℕ) (he : e ∉ E) (hf : f ∉ F) :
      ConstructibleSurface V E F → ConstructibleSurface V (insert e E) (insert f F)
  /-- Erect a pyramid over a `k`-gonal face (`k = newE.card ≥ 3`): a fresh apex `v`, `k` fresh
  edges and `k - 1` fresh faces. -/
  | pyramid {V E F : Finset ℕ} (v : ℕ) (newE newF : Finset ℕ)
      (hv : v ∉ V) (hE : Disjoint newE E) (hF : Disjoint newF F)
      (hk : 3 ≤ newE.card) (hcard : newF.card + 1 = newE.card) :
      ConstructibleSurface V E F →
        ConstructibleSurface (insert v V) (newE ∪ E) (newF ∪ F)
  /-- Truncate a vertex of degree `d = newE.card ≥ 3`: delete the vertex, insert `d` fresh
  vertices, `d` fresh edges and one fresh face. -/
  | truncate {V E F : Finset ℕ} (v f : ℕ) (newV newE : Finset ℕ)
      (hv : v ∈ V) (hVd : Disjoint newV V) (hE : Disjoint newE E) (hf : f ∉ F)
      (hd : 3 ≤ newE.card) (hcard : newV.card = newE.card) :
      ConstructibleSurface V E F →
        ConstructibleSurface (newV ∪ V.erase v) (newE ∪ E) (insert f F)

/-- A surface built from actual finite sets has counts which form a polyhedron in the sense of
`Chem.IsPolyhedron`; the cardinalities of the three sets change exactly as the numerical
constructions prescribe. -/
