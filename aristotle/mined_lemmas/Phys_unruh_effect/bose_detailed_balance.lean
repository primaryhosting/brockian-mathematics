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

theorem bose_detailed_balance (hbar c a kB E : ℝ) (hc : 0 < c) (ha : 0 < a) (hhbar : 0 < hbar)
    (hkB : 0 < kB) (hE : 0 < E) :
    bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
      = Real.exp (-(E / (kB * unruhTemperature hbar c a kB)))
    ∧ bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
      = Real.exp (-(2 * π * c * E) / (hbar * a)) := by
  have hxe := unruh_exponent hbar c a kB E hc ha hhbar hkB
  have hxpos : 0 < E / (kB * unruhTemperature hbar c a kB) := by
    rw [hxe]
    have h1 : 0 < hbar * a := by positivity
    have h2 : 0 < 2 * π * c * E := by positivity
    exact div_pos h2 h1
  have hb : bose E (unruhTemperature hbar c a kB) kB
      = 1 / (Real.exp (E / (kB * unruhTemperature hbar c a kB)) - 1) := rfl
  have hmain := bose_ratio _ hxpos
  rw [hb]
  refine ⟨hmain, ?_⟩
  rw [hmain, hxe]
  congr 1
  ring

/-! ### Main theorem -/

/-- **The Unruh effect.**

For an observer with constant proper acceleration `a` moving through the Minkowski vacuum of a
massless scalar field:

0. the four-velocity of the worldline is normalised (`τ` is the proper time);
1. the Rindler worldline `τ ↦ ((c/a) sinh (aτ/c), (c²/a) cosh (aτ/c))` has constant proper
   acceleration `a`;
2. the invariant interval between two of its points is `(2c²/a)² sinh²(a(τ-τ')/(2c))`;
3. the vacuum Wightman function restricted to the worldline is the standard massless
   two-point function `-ℏ/(4π² s²)` of that interval;
4. that Wightman function is periodic in imaginary proper time with period `ℏ / (k_B T)`
   (the KMS condition, i.e. thermality at temperature `T`) for
   `T = T_U := ℏ a / (2 π c k_B)`, the period being `2 π c / a`;
5. the corresponding occupation numbers obey Planckian detailed balance
   `n/(n+1) = exp(-E/(k_B T_U)) = exp(-2π c E/(ℏ a))`;
6. and the temperature so identified is `T_U = ℏ a / (2 π c k_B)`, the **Unruh temperature**.
-/
