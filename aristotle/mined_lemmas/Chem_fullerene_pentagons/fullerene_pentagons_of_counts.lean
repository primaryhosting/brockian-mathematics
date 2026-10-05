/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

/-- A combinatorial description of a trivalent (3-regular) convex polyhedron whose
faces are only pentagons and hexagons:

* `V`, `E`, `F` are the numbers of vertices, edges and faces;
* `euler` is Euler's formula `V - E + F = 2`, written additively to avoid `Nat`-subtraction;
* `trivalent` says every vertex has degree three (each edge has two endpoints);
* `faces` splits the faces into `pentagons` and `hexagons`;
* `edge_count` counts edge–face incidences (each edge lies on exactly two faces).
-/
structure Polyhedron where
  V : Nat
  E : Nat
  F : Nat
  pentagons : Nat
  hexagons : Nat
  euler : V + F = E + 2
  trivalent : 3 * V = 2 * E
  faces : F = pentagons + hexagons
  edge_count : 5 * pentagons + 6 * hexagons = 2 * E

/-- Explicit-hypothesis form of the fullerene pentagon count: if `V`, `E`, `F` satisfy
Euler's formula, every vertex is trivalent, and the `F` faces consist of `p` pentagons
and `h` hexagons, then `p = 12`. -/

theorem fullerene_pentagons_of_counts {V E F p h : Nat}
    (euler : V + F = E + 2) (trivalent : 3 * V = 2 * E)
    (faces : F = p + h) (edge_count : 5 * p + 6 * h = 2 * E) : p = 12 := by
  omega

/-- **Fullerene pentagon count.** Any trivalent polyhedron all of whose faces are
pentagons or hexagons has exactly 12 pentagonal faces. -/
