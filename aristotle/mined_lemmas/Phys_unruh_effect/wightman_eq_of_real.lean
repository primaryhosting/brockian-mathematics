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

theorem wightman_eq_of_real (hbar c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (τ : ℝ) :
    wightman hbar c a (τ : ℂ) = ((-(hbar / (4 * π ^ 2)) / intervalSq c a τ 0 : ℝ) : ℂ) := by
  have hI := intervalSq_eq c a hc ha τ 0
  have hτ : a * (τ - 0) / (2 * c) = a * τ / (2 * c) := by ring_nf
  rw [hτ] at hI
  have hsinh : Complex.sinh ((a : ℂ) * (τ : ℂ) / (2 * (c : ℂ)))
      = ((Real.sinh (a * τ / (2 * c)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sinh]
    push_cast
    ring_nf
  rw [wightman, hsinh, hI]
  by_cases h0 : Real.sinh (a * τ / (2 * c)) = 0
  · rw [h0]
    simp
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have h0' : ((Real.sinh (a * τ / (2 * c)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi
    push_cast
    field_simp
    ring

/-! ### KMS condition: thermality at the Unruh temperature -/

