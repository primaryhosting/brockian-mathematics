/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Combinatorial data of a trivalent (3-regular) convex polyhedron all of whose faces
are pentagons or hexagons — the shape of a fullerene molecule.

* `V`, `E`, `F` are the numbers of vertices, edges and faces;
* `P` and `H` are the numbers of pentagonal and hexagonal faces;
* `euler` is Euler's formula `V - E + F = 2` (written additively to avoid ℕ-subtraction);
* `trivalent` : every vertex lies on exactly 3 edges, and every edge has 2 endpoints,
  so `3V = 2E`;
* `faces_split` : every face is a pentagon or a hexagon;
* `edge_count` : every face of size `k` contributes `k` face-edge incidences, and every
  edge lies on exactly 2 faces, so `5P + 6H = 2E`. -/
structure Fullerene where
  V : Nat
  E : Nat
  F : Nat
  P : Nat
  H : Nat
  euler : V + F = E + 2
  trivalent : 3 * V = 2 * E
  faces_split : F = P + H
  edge_count : 5 * P + 6 * H = 2 * E

/-- **Fullerene pentagon count.** A trivalent polyhedron whose faces are all pentagons
or hexagons has exactly 12 pentagonal faces. -/

def buckminsterfullerene : Fullerene where
  V := 60
  E := 90
  F := 32
  P := 12
  H := 20
  euler := by omega
  trivalent := by omega
  faces_split := by omega
  edge_count := by omega

/-- A carbon fullerene C₆₀-style consequence: the number of pentagons is independent of
the number of hexagons, which may be arbitrary. -/
example (X Y : Fullerene) : X.P = Y.P := by
  rw [fullerene_pentagons X, fullerene_pentagons Y]

end Chem

