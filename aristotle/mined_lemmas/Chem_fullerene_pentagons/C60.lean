/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Combinatorial data of a trivalent (3-regular) convex polyhedron all of whose faces are
pentagons or hexagons — the shape of a fullerene molecule.

* `V`, `E`, `F` are the numbers of vertices, edges and faces;
* `pent`, `hex` are the numbers of pentagonal and hexagonal faces;
* `euler` is Euler's polyhedron formula `V - E + F = 2`, written subtraction-free as
  `V + F = E + 2`;
* `trivalent` is the handshake identity for a 3-regular graph: each of the `V` vertices meets
  `3` edges and each edge has `2` endpoints;
* `faces` says every face is a pentagon or a hexagon;
* `faceDegreeSum` counts edge-face incidences: each pentagon has `5` sides, each hexagon `6`,
  and every edge borders exactly `2` faces. -/
structure Fullerene where
  V : Nat
  E : Nat
  F : Nat
  pent : Nat
  hex : Nat
  euler : V + F = E + 2
  trivalent : 3 * V = 2 * E
  faces : pent + hex = F
  faceDegreeSum : 5 * pent + 6 * hex = 2 * E

/-- **Fullerene pentagon count.** A trivalent polyhedron whose faces are all pentagons or
hexagons has exactly `12` pentagonal faces. -/

def C60 : Fullerene where
  V := 60
  E := 90
  F := 32
  pent := 12
  hex := 20
  euler := by decide
  trivalent := by decide
  faces := by decide
  faceDegreeSum := by decide

#print axioms fullerene_pentagons

end Chem

