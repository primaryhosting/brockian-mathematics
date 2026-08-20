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

noncomputable def corrExponent (J T : ℝ) : ℝ := T / (2 * Real.pi * J)

/-- The logarithm `log (L / a)` occurring in the vortex free energy is positive
for a system larger than the vortex core. -/
