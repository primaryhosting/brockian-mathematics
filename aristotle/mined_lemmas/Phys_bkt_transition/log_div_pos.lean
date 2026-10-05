/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-!
## The Berezinskii–Kosterlitz–Thouless transition of the 2D XY model

The BKT transition is the *topological* phase transition of the two–dimensional XY model
(planar rotators with nearest–neighbour coupling `J` on a two–dimensional lattice of spacing
`a`, confined to a box of linear size `L`).  Its mechanism is the *unbinding of vortices*,
and the transition temperature is located by the classical Kosterlitz–Thouless
*energy–entropy* balance:

* a single vortex of unit topological charge in a box of size `L` costs the elastic energy
  `E(L) = π J log (L / a)` (the spin–wave energy of the winding configuration, obtained by
  integrating `J/2 |∇θ|² = J/(2 r²)` over the annulus `a ≤ r ≤ L`);
* the vortex core can be placed at any of the `(L/a)²` lattice sites, so its entropy is
  `S(L) = k_B log ((L/a)²) = 2 k_B log (L / a)` (we work in units `k_B = 1`);
* hence the free energy of a single free vortex is
  `F(T, L) = E(L) - T S(L) = (π J - 2 T) log (L / a)`.

Below `T_BKT = π J / 2` the free energy of an isolated vortex is positive and *diverges*
with the system size, so vortices only occur in tightly bound neutral pairs: the system is
in the quasi–long–range–ordered (topologically ordered) phase.  Above `T_BKT` the free
energy of an isolated vortex is negative and diverges to `-∞`, so free vortices proliferate
and destroy the quasi–long–range order.  The temperature `T_BKT` is the unique temperature
at which this change of sign occurs; this is the content of `Phys.bkt_transition` below.
-/

/-- Elastic (spin–wave) energy of a single unit–charge vortex of core size `a`
in a two–dimensional box of linear size `L`, at coupling `J`. -/

lemma log_div_pos {L a : ℝ} (ha : 0 < a) (haL : a < L) : 0 < Real.log (L / a) :=
  Real.log_pos ((one_lt_div ha).mpr haL)

