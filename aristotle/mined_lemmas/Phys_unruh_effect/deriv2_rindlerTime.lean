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

theorem deriv2_rindlerTime (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    deriv (deriv (fun s => c * rindlerTime c a s)) = fun τ => c * (a / c) * Real.sinh (a * τ / c) := by
  have h1 : deriv (fun s => c * rindlerTime c a s) = fun τ => c * Real.cosh (a * τ / c) := by
    funext τ
    have h : HasDerivAt (fun s : ℝ => c * rindlerTime c a s)
        (c * ((c / a) * (Real.cosh (a * τ / c) * (a / c)))) τ :=
      (((Real.hasDerivAt_sinh _).comp τ (hasDerivAt_lin a c τ)).const_mul _).const_mul _
    rw [h.deriv]; field_simp
  rw [h1]
  funext τ
  have h : HasDerivAt (fun s : ℝ => c * Real.cosh (a * s / c))
      (c * (Real.sinh (a * τ / c) * (a / c))) τ :=
    ((Real.hasDerivAt_cosh _).comp τ (hasDerivAt_lin a c τ)).const_mul _
  rw [h.deriv]; ring

/-! ### The worldline has constant proper acceleration `a` -/

/-- The four-velocity of the Rindler worldline is normalised, `u · u = c²`; equivalently, `τ`
really is the proper time along the worldline. -/
