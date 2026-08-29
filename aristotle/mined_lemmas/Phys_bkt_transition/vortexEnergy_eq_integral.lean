/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-!
## The Berezinskii–Kosterlitz–Thouless transition of the 2D XY model

We formalise the Kosterlitz–Thouless *energy–entropy* criterion, which is the
mathematical content identifying the BKT topological phase transition.

For the two-dimensional XY model with spin stiffness (coupling) `J`, a single
unit-charge vortex centred in a box of linear size `L`, with a core cut off at
radius `a`, has phase gradient of modulus `|∇θ(r)| = 1/r`, hence spin-wave energy
density `(J/2)|∇θ|² = (J/2)(1/r)²`.  Integrating this over the annulus
`a ≤ r ≤ L` (area element `2πr dr`) gives the logarithmically divergent vortex
energy `E = πJ log (L/a)`.

The vortex core may sit at any of `(L/a)²` distinguishable positions, so its
entropy (in units of `k_B`) is `S = log ((L/a)²) = 2 log (L/a)`.

The free energy of a single free vortex is therefore
`F = E - T S = (πJ - 2T) log (L/a)`,
whose sign changes at the *BKT temperature* `T_BKT = πJ/2` (with `k_B = 1`).

* For `T < T_BKT` we have `F > 0`: isolated vortices are thermodynamically
  suppressed, they occur only in bound vortex–antivortex pairs, and the system is
  in the quasi-long-range-ordered (topologically ordered) phase.
* For `T > T_BKT` we have `F < 0`: free vortices proliferate, unbinding destroys
  the quasi-long-range order, and the system is disordered.
* At `T = T_BKT` the free energy vanishes; `T_BKT` is the unique such
  temperature, and there the stiffness-to-temperature ratio takes the universal
  value `J / T_BKT = 2/π` (the universal jump of the superfluid stiffness).
-/

/-- Radial energy profile of a single unit-charge vortex of the 2D XY model with
spin stiffness `J`: the spin-wave energy density `(J/2)|∇θ|² = (J/2)(1/r)²`
multiplied by the circumference `2πr` of the circle of radius `r`. -/

theorem vortexEnergy_eq_integral (J a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    (∫ r in a..L, vortexEnergyDensity J r) = vortexEnergy J a L := by
  have hcongr : ∀ r ∈ Set.uIcc a L, vortexEnergyDensity J r = (Real.pi * J) * (1 / r) := by
    intro r hr
    have hr0 : r ≠ 0 := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact ne_of_gt (lt_of_lt_of_le ha h.1)
      · exact ne_of_gt (lt_of_lt_of_le hL h.1)
    unfold vortexEnergyDensity
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos ha hL]
  rfl

/-- The vortex entropy is `2 log (L/a)`. -/
