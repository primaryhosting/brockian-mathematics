/-
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fullerene Pentagons

A trivalent polyhedron all of whose faces are pentagons or hexagons has exactly 12 pentagons.
-/

namespace Chem

/-- Arithmetic core of the fullerene count: if `p` faces are pentagons and `h` faces are
hexagons, every vertex has degree `3`, and Euler's formula `V - E + F = 2` holds, then
`p = 12`. -/

theorem fullerene_pentagons_arith (V E F p h : ℕ)
    (euler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (trivalent : 2 * E = 3 * V)
    (face_count : p + h = F)
    (edge_count : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-- **Fullerene pentagon count.**

Let a polyhedron be given combinatorially by a finite vertex set `𝒱`, a finite edge set `ℰ`
and a finite face set `ℱ`, satisfying Euler's formula.  Assume:

* it is *trivalent*: each vertex lies on exactly `3` edges, so `2 * #ℰ = 3 * #𝒱`
  (each edge has two endpoints);
* every face is a pentagon or a hexagon, `size f ∈ {5, 6}`, and each edge lies on exactly two
  faces, so the face sizes sum to `2 * #ℰ`.

Then exactly `12` faces are pentagons. -/
