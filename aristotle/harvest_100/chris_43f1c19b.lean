/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **Fullerene pentagon count.**

Let a polyhedron have `V` vertices, `E` edges and `F` faces, of which `P` are pentagons and
`H` are hexagons.  Assume:

* Euler's formula `V - E + F = 2`, stated subtraction-free as `V + F = E + 2`;
* trivalence: every vertex meets exactly three edges, so `3 * V = 2 * E`;
* every face is a pentagon or a hexagon: `F = P + H`, and counting edge-face incidences
  (each edge lies on exactly two faces) gives `5 * P + 6 * H = 2 * E`.

Then the polyhedron has exactly `12` pentagonal faces — the combinatorial reason why every
fullerene molecule contains precisely twelve pentagonal rings.

Proof: from `3V = 2E` and `V + F = E + 2` we get `3P + 3H = 3F = E + 6`, i.e. `6P + 6H = 2E + 12`,
while `2E = 5P + 6H`; subtracting yields `P = 12`.  (The `omega` decision procedure for linear
integer arithmetic performs exactly this elimination.)
-/
theorem fullerene_pentagons
    (V E F P H : Nat)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : F = P + H)
    (edge_face : 5 * P + 6 * H = 2 * E) :
    P = 12 := by
  omega

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

