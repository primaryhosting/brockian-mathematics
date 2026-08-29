import Mathlib
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Unruh effect: an observer moving with constant proper acceleration `a` through the
Minkowski vacuum of a massless scalar field perceives a thermal bath at the temperature

                            T = ℏ a / (2 π c k_B).

The formalisation below is organised as follows.

* `Phys.rindlerTime`, `Phys.rindlerPos` : the uniformly accelerated (Rindler) worldline,
  parametrised by proper time `τ`.
* `Phys.properAccelSq` : the Minkowski square of the four-acceleration; it is shown to be
  identically `a ^ 2`, i.e. the worldline really has constant proper acceleration `a`.
* `Phys.intervalSq` : the invariant interval between two points of the worldline; it is shown
  to equal `(2 c ^ 2 / a) ^ 2 * sinh (a (τ - τ') / (2 c)) ^ 2`.
* `Phys.wightman` : the vacuum two-point (Wightman) function of a massless scalar field
  restricted to the accelerated worldline and continued to complex proper time; it is shown to
  be the standard `-ℏ / (4 π ^ 2 s ^ 2)` expression in terms of the invariant interval.
* `Phys.unruhTemperature` : the Unruh temperature `ℏ a / (2 π c k_B)`.
* The KMS (Kubo–Martin–Schwinger) property: the Wightman function is periodic in imaginary
  proper time with period `ℏ / (k_B T)` exactly when `T` is the Unruh temperature.  Periodicity
  in imaginary time with period `ℏ / (k_B T)` is precisely the statement that the state looks
  thermal at temperature `T`.
* `Phys.bose` : the Bose–Einstein occupation number, satisfying detailed balance at the Unruh
  temperature, `n / (n + 1) = exp (-2 π c E / (ℏ a))`.

The main theorem `Phys.unruh_effect` collects these statements.
-/

namespace Phys

open Real

/-- Time coordinate of the uniformly accelerated (Rindler) worldline, as a function of the
proper time `τ`. -/

theorem unruh_effect (hbar c a kB : ℝ) (hc : 0 < c) (ha : 0 < a) (hhbar : 0 < hbar)
    (hkB : 0 < kB) :
    (∀ τ : ℝ, (c * deriv (rindlerTime c a) τ) ^ 2 - (deriv (rindlerPos c a) τ) ^ 2 = c ^ 2) ∧
    (∀ τ : ℝ, properAccelSq c a τ = a ^ 2) ∧
    (∀ τ τ' : ℝ, intervalSq c a τ τ'
        = (2 * c ^ 2 / a) ^ 2 * Real.sinh (a * (τ - τ') / (2 * c)) ^ 2) ∧
    (∀ τ : ℝ, wightman hbar c a (τ : ℂ)
        = ((-(hbar / (4 * π ^ 2)) / intervalSq c a τ 0 : ℝ) : ℂ)) ∧
    (hbar / (kB * unruhTemperature hbar c a kB) = 2 * π * c / a) ∧
    (∀ z : ℂ, wightman hbar c a
        (z - Complex.I * ((hbar / (kB * unruhTemperature hbar c a kB) : ℝ) : ℂ))
        = wightman hbar c a z) ∧
    (∀ E : ℝ, 0 < E →
      bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
        = Real.exp (-(E / (kB * unruhTemperature hbar c a kB)))) ∧
    unruhTemperature hbar c a kB = hbar * a / (2 * π * c * kB) := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have ha' : a ≠ 0 := ne_of_gt ha
  refine ⟨fun τ => fourVelocity_norm c a hc' ha' τ, fun τ => properAccelSq_eq c a hc' ha' τ, fun τ τ' => intervalSq_eq c a hc' ha' τ τ',
    fun τ => wightman_eq_of_real hbar c a hc' ha' τ,
    kms_period hbar c a kB (ne_of_gt hhbar) (ne_of_gt hkB),
    fun z => wightman_kms hbar c a kB hc' ha' (ne_of_gt hhbar) (ne_of_gt hkB) z, ?_, rfl⟩
  intro E hE
  exact (bose_detailed_balance hbar c a kB E hc ha hhbar hkB hE).1

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

