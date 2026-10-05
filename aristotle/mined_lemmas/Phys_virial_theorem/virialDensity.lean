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

noncomputable def virialDensity (V1 : ℝ → ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ x) * (((x * V1 x : ℝ) : ℂ) * ψ x)

/-- The boundary flux associated with the virial operator `A = x d/dx`.  It is the
quantity whose derivative is `2 * (kinetic density) - (virial density)`; for a bound
state it decays to `0` at `±∞`, which is what makes the virial theorem hold.

Explicitly, `virialFlux m E V ψ ψ1 x =
  -(1/2m) ψ*(x) ψ'(x) + x ((1/2m) |ψ'(x)|² - (V(x) - E) |ψ(x)|²)`. -/
