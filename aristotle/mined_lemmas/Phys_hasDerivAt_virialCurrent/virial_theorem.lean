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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

theorem virial_theorem (hbar mass E : ℝ) (psi dpsi ddpsi V dV : ℝ → ℝ)
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    -- stationary Schrödinger equation `H ψ = E ψ`
    (hSch : ∀ x, -(hbar ^ 2 / (2 * mass)) * ddpsi x + V x * psi x = E * psi x)
    -- integrability of the kinetic and virial densities
    (hT : Integrable (fun x => dpsi x ^ 2) volume)
    (hW : Integrable (fun x => x * dV x * psi x ^ 2) volume)
    -- boundary terms vanish (the state is bound)
    (hb1 : Tendsto (fun x => x * dpsi x ^ 2) atBot (𝓝 0))
    (hb2 : Tendsto (fun x => x * dpsi x ^ 2) atTop (𝓝 0))
    (hb3 : Tendsto (fun x => psi x * dpsi x) atBot (𝓝 0))
    (hb4 : Tendsto (fun x => psi x * dpsi x) atTop (𝓝 0))
    (hb5 : Tendsto (fun x => x * (V x - E) * psi x ^ 2) atBot (𝓝 0))
    (hb6 : Tendsto (fun x => x * (V x - E) * psi x ^ 2) atTop (𝓝 0)) :
    2 * ∫ x, (hbar ^ 2 / (2 * mass)) * dpsi x ^ 2
      = ∫ x, x * dV x * psi x ^ 2 := by
  set c : ℝ := hbar ^ 2 / (2 * mass)
  have hSch' : ∀ x, c * ddpsi x = (V x - E) * psi x := fun x => by linarith [hSch x]
  have hderiv := hasDerivAt_virialCurrent c E psi dpsi ddpsi V dV hpsi hdpsi hV hSch'
  have hint : Integrable (fun x => 2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) volume :=
    (hT.const_mul (2 * c)).sub hW
  have hlim_bot : Tendsto (virialCurrent c E psi dpsi V) atBot (𝓝 0) := by
    have : Tendsto (fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x)
        - x * (V x - E) * psi x ^ 2) atBot (𝓝 (c * (0 + 0) - 0)) :=
      ((hb1.add hb3).const_mul c).sub hb5
    simpa [virialCurrent] using this
  have hlim_top : Tendsto (virialCurrent c E psi dpsi V) atTop (𝓝 0) := by
    have : Tendsto (fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x)
        - x * (V x - E) * psi x ^ 2) atTop (𝓝 (c * (0 + 0) - 0)) :=
      ((hb2.add hb4).const_mul c).sub hb6
    simpa [virialCurrent] using this
  have key : ∫ x, (2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) = 0 := by
    simpa using
      MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint hlim_bot hlim_top
  rw [integral_sub (hT.const_mul (2 * c)) hW] at key
  have hTc : ∫ x, c * dpsi x ^ 2 = c * ∫ x, dpsi x ^ 2 := integral_const_mul c _
  have h2c : ∫ x, 2 * c * dpsi x ^ 2 = 2 * c * ∫ x, dpsi x ^ 2 := by
    simpa [mul_assoc] using integral_const_mul (2 * c) (fun x => dpsi x ^ 2)
  rw [h2c] at key
  rw [hTc]
  linarith

/-! ### Non-vacuity: the harmonic-oscillator ground state satisfies all the hypotheses -/

/-- `x ^ n * exp (-x²) → 0` as `x → +∞`. -/
