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

theorem virial_theorem {m E : ℝ} (hm : m ≠ 0) {V V1 : ℝ → ℝ} {ψ ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : ∀ x, HasDerivAt ψ (ψ1 x) x)
    (hψ2 : ∀ x, HasDerivAt ψ1 (ψ2 x) x)
    (hV1 : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -(1 / (2 * m)) * ψ2 x + ((V x : ℝ) : ℂ) * ψ x = (E : ℂ) * ψ x)
    (hTint : Integrable (kineticDensity m ψ ψ2))
    (hWint : Integrable (virialDensity V1 ψ))
    (hbot : Tendsto (virialFlux m E V ψ ψ1) atBot (𝓝 0))
    (htop : Tendsto (virialFlux m E V ψ ψ1) atTop (𝓝 0)) :
    2 * ∫ x, kineticDensity m ψ ψ2 x = ∫ x, virialDensity V1 ψ x := by
  have hInt : Integrable
      (fun x => 2 * kineticDensity m ψ ψ2 x - virialDensity V1 ψ x) :=
    (hTint.const_mul 2).sub hWint
  have hzero : ∫ x, (2 * kineticDensity m ψ ψ2 x - virialDensity V1 ψ x) = 0 := by
    have := integral_of_hasDerivAt_of_tendsto
      (hasDerivAt_virialFlux hm hψ1 hψ2 hV1 hSch) hInt hbot htop
    simpa using this
  rw [integral_sub (hTint.const_mul 2) hWint, integral_const_mul] at hzero
  linear_combination hzero

end Phys

