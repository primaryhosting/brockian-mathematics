/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Statement: State the Unruh temperature T = ℏa/(2πck) seen by a uniformly accelerated observer.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Real

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`, expressed in terms of the reduced Planck constant `hbar`, the speed of
light `c` and Boltzmann's constant `kB`. -/
noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- The Planck (Bose–Einstein) occupation number at temperature `T` for a mode of
angular frequency `ω`. -/
noncomputable def planckOccupation (hbar kB T ω : ℝ) : ℝ :=
  1 / (Real.exp (hbar * ω / (kB * T)) - 1)

/-- The occupation number of the Rindler (uniformly accelerated) detector for a mode of
angular frequency `ω`: the Bogoliubov transformation between Minkowski and Rindler modes
produces the factor `exp (2 π c ω / a)` in the denominator. -/
noncomputable def rindlerOccupation (a c ω : ℝ) : ℝ :=
  1 / (Real.exp (2 * Real.pi * c * ω / a) - 1)

/-- **Unruh effect.**  A uniformly accelerated observer with proper acceleration `a > 0`
sees the Minkowski vacuum as a thermal bath.  The temperature of that bath is

  `T = ℏ a / (2 π c k_B)`,

which is: (1) positive; (2) the temperature whose Boltzmann factor `exp (-ℏω/(k_B T))`
reproduces, for every mode frequency `ω`, the Rindler thermality factor
`exp (-2 π c ω / a)` obtained from the Bogoliubov coefficients; (3) the *unique* positive
temperature with that property; and (4) the temperature whose Planck spectrum coincides
with the spectrum registered by the accelerated detector. -/
theorem unruh_effect (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) :
    0 < unruhTemperature hbar a c kB ∧
    (∀ ω : ℝ, Real.exp (-(hbar * ω / (kB * unruhTemperature hbar a c kB))) =
        Real.exp (-(2 * Real.pi * c * ω / a))) ∧
    (∀ T : ℝ, 0 < T →
        (∀ ω : ℝ, Real.exp (-(hbar * ω / (kB * T))) = Real.exp (-(2 * Real.pi * c * ω / a))) →
        T = unruhTemperature hbar a c kB) ∧
    (∀ ω : ℝ, planckOccupation hbar kB (unruhTemperature hbar a c kB) ω
        = rindlerOccupation a c ω) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < 2 * Real.pi * c * kB := by positivity
  have hT : 0 < unruhTemperature hbar a c kB := by
    unfold unruhTemperature
    positivity
  -- the key algebraic identity
  have key : ∀ ω : ℝ, hbar * ω / (kB * unruhTemperature hbar a c kB)
      = 2 * Real.pi * c * ω / a := by
    intro ω
    unfold unruhTemperature
    field_simp
  refine ⟨hT, fun ω => by rw [key ω], ?_, fun ω => by
    unfold planckOccupation rindlerOccupation; rw [key ω]⟩
  intro T hTpos hall
  have h1 := hall 1
  rw [Real.exp_eq_exp] at h1
  have h2 : hbar / (kB * T) = 2 * Real.pi * c / a := by
    have : hbar * 1 / (kB * T) = 2 * Real.pi * c * 1 / a := by linarith
    simpa using this
  unfold unruhTemperature
  field_simp at h2 ⊢
  nlinarith [h2, hTpos.le, ha.le]

end Phys

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

