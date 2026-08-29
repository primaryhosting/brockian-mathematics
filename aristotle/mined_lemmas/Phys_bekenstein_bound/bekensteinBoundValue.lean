/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

set_option grind.warning false

namespace Phys

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal thermodynamic
entropy of a system of total energy `E` that fits inside a sphere of radius `R`,
where `k` is Boltzmann's constant, `hbar` the reduced Planck constant and `c` the
speed of light. -/

noncomputable def bekensteinBoundValue (k R E hbar c : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)` of a black hole of horizon
area `A`. -/
