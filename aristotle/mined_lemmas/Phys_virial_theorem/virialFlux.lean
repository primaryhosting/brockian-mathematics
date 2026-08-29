import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

open MeasureTheory Filter Topology

/-- The (unnormalized) kinetic energy density `ψ* (T ψ)` of a one-dimensional
wave function `ψ` with second derivative `ψ2`, for a particle of mass `m`
(in units with `ℏ = 1`), i.e. `T = -(1/2m) d²/dx²`. -/

noncomputable def virialFlux (m E : ℝ) (V : ℝ → ℝ) (ψ ψ1 : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(1 / (2 * m)) * (starRingEnd ℂ) (ψ x) * ψ1 x
    + (x : ℂ) * ((1 / (2 * m)) * (starRingEnd ℂ) (ψ1 x) * ψ1 x
        - (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ x) * ψ x)

/-- From the time-independent Schrödinger equation, the second derivative of `ψ`
is `2m (V - E) ψ`. -/
