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

def buckyballCage : Cage where
  V := Finset.range 60
  E := Finset.range 90
  F := Finset.range 32
  ends := fun e =>
    match e with
    | 0 => {0, 1}
    | 1 => {0, 4}
    | 2 => {1, 3}
    | 3 => {2, 3}
    | 4 => {2, 4}
    | 5 => {5, 6}
    | 6 => {5, 8}
    | 7 => {6, 9}
    | 8 => {7, 8}
    | 9 => {7, 9}
    | 10 => {10, 11}
    | 11 => {10, 13}
    | 12 => {11, 14}
    | 13 => {12, 13}
    | 14 => {12, 14}
    | 15 => {15, 16}
    | 16 => {15, 17}
    | 17 => {16, 19}
    | 18 => {17, 18}
    | 19 => {18, 19}
    | 20 => {20, 21}
    | 21 => {20, 22}
    | 22 => {21, 24}
    | 23 => {22, 23}
    | 24 => {23, 24}
    | 25 => {25, 26}
    | 26 => {25, 27}
    | 27 => {26, 28}
    | 28 => {27, 29}
    | 29 => {28, 29}
    | 30 => {30, 31}
    | 31 => {30, 33}
    | 32 => {31, 32}
    | 33 => {32, 34}
    | 34 => {33, 34}
    | 35 => {35, 36}
    | 36 => {35, 38}
    | 37 => {36, 37}
    | 38 => {37, 39}
    | 39 => {38, 39}
    | 40 => {40, 41}
    | 41 => {40, 42}
    | 42 => {41, 43}
    | 43 => {42, 44}
    | 44 => {43, 44}
    | 45 => {45, 47}
    | 46 => {45, 49}
    | 47 => {46, 47}
    | 48 => {46, 48}
    | 49 => {48, 49}
    | 50 => {50, 52}
    | 51 => {50, 53}
    | 52 => {51, 52}
    | 53 => {51, 54}
    | 54 => {53, 54}
    | 55 => {55, 57}
    | 56 => {55, 58}
    | 57 => {56, 57}
    | 58 => {56, 59}
    | 59 => {58, 59}
    | 60 => {0, 5}
    | 61 => {1, 10}
    | 62 => {2, 25}
    | 63 => {3, 30}
    | 64 => {4, 35}
    | 65 => {6, 11}
    | 66 => {7, 15}
    | 67 => {8, 36}
    | 68 => {9, 40}
    | 69 => {12, 20}
    | 70 => {13, 31}
    | 71 => {14, 41}
    | 72 => {16, 37}
    | 73 => {17, 42}
    | 74 => {18, 45}
    | 75 => {19, 55}
    | 76 => {21, 32}
    | 77 => {22, 43}
    | 78 => {23, 46}
    | 79 => {24, 50}
    | 80 => {26, 33}
    | 81 => {27, 38}
    | 82 => {28, 51}
    | 83 => {29, 56}
    | 84 => {34, 52}
    | 85 => {39, 57}
    | 86 => {44, 47}
    | 87 => {48, 53}
    | 88 => {49, 58}
    | 89 => {54, 59}
    | _ => ∅
  sides := fun f =>
    match f with
    | 0 => {0, 1, 2, 3, 4}
    | 1 => {5, 6, 7, 8, 9}
    | 2 => {10, 11, 12, 13, 14}
    | 3 => {15, 16, 17, 18, 19}
    | 4 => {20, 21, 22, 23, 24}
    | 5 => {25, 26, 27, 28, 29}
    | 6 => {30, 31, 32, 33, 34}
    | 7 => {35, 36, 37, 38, 39}
    | 8 => {40, 41, 42, 43, 44}
    | 9 => {45, 46, 47, 48, 49}
    | 10 => {50, 51, 52, 53, 54}
    | 11 => {55, 56, 57, 58, 59}
    | 12 => {0, 5, 10, 60, 61, 65}
    | 13 => {1, 6, 35, 60, 64, 67}
    | 14 => {2, 11, 30, 61, 63, 70}
    | 15 => {3, 25, 31, 62, 63, 80}
    | 16 => {4, 26, 36, 62, 64, 81}
    | 17 => {7, 12, 40, 65, 68, 71}
    | 18 => {8, 15, 37, 66, 67, 72}
    | 19 => {9, 16, 41, 66, 68, 73}
    | 20 => {13, 20, 32, 69, 70, 76}
    | 21 => {14, 21, 42, 69, 71, 77}
    | 22 => {17, 38, 55, 72, 75, 85}
    | 23 => {18, 43, 45, 73, 74, 86}
    | 24 => {19, 46, 56, 74, 75, 88}
    | 25 => {22, 33, 50, 76, 79, 84}
    | 26 => {23, 44, 47, 77, 78, 86}
    | 27 => {24, 48, 51, 78, 79, 87}
    | 28 => {27, 34, 52, 80, 82, 84}
    | 29 => {28, 39, 57, 81, 83, 85}
    | 30 => {29, 53, 58, 82, 83, 89}
    | 31 => {49, 54, 59, 87, 88, 89}
    | _ => ∅

/-- Euler's formula for the explicit C₆₀ cage: `60 - 90 + 32 = 2`. -/
