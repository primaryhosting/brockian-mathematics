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

noncomputable def unruhTemperature (hbar c a kB : ℝ) : ℝ := hbar * a / (2 * π * c * kB)

/-- The vacuum Wightman two-point function of a massless scalar field, restricted to the
uniformly accelerated worldline and analytically continued to complex proper time `z`.  (The
`iε`-prescription of the Wightman function is implemented by the analytic continuation.) -/
