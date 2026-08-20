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

set_option grind.warning false

namespace Phys

/-- The Kosterlitz–Thouless transition temperature of the 2D XY model with spin
stiffness (coupling) `J`, in units where the Boltzmann constant is `1`:
`T_BKT = π J / 2`. -/

noncomputable def bktTemperature (J : ℝ) : ℝ := Real.pi * J / 2

/-- Free energy cost `F = E - T S` of inserting a single vortex of core size `a`
into a two-dimensional XY system of linear size `L`.

The energy of an isolated vortex is `E = π J log (L / a)`, and its entropy is
`S = 2 log (L / a)` (there are `(L / a) ^ 2` distinguishable positions for the
core), so `F = (π J - 2 T) log (L / a)`. -/
