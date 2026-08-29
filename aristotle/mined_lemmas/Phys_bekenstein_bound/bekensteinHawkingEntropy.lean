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

noncomputable def bekensteinHawkingEntropy (k A hbar c G : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * G * hbar)

/-- Geroch-process step: the horizon-area increase `ΔA = 8 π G E R / c⁴` produced by
lowering a body of energy `E` and radius `R` into a black hole contributes exactly the
Bekenstein bound to the black hole entropy. -/
