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

noncomputable def kineticDensity (m : ℝ) (ψ ψ2 : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ x) * (-(1 / (2 * m)) * ψ2 x)

/-- The (unnormalized) virial density `ψ* (x V'(x)) ψ`, i.e. the integrand of
the expectation value `⟨r · ∇V⟩` in one dimension, where `V1` is the derivative
of the potential `V`. -/
