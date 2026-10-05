/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial

namespace Frontier

/-! ### Hermite polynomial facts -/

/-- The derivative of the `(n+1)`-st probabilists' Hermite polynomial. -/

theorem hasDerivAt_hermiteGauss' (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss' n)
      ((x ^ 2 / 4 - ((n : ℝ) + 1 / 2)) * hermiteGauss n x) x := by
  have hode : ∀ y : ℝ, aeval y (derivative (derivative (hermite n)))
      = y * aeval y (derivative (hermite n)) - (n : ℝ) * aeval y (hermite n) := by
    intro y
    have := congrArg (fun p : Polynomial ℤ => aeval y p) (hermite_ode n)
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_zero] at this
    push_cast at this
    linarith
  have h1 : HasDerivAt (fun y : ℝ => aeval y (derivative (hermite n)))
      (aeval x (derivative (derivative (hermite n)))) x :=
    Polynomial.hasDerivAt_aeval _ _
  have h0 : HasDerivAt (fun y : ℝ => aeval y (hermite n)) (aeval x (derivative (hermite n))) x :=
    Polynomial.hasDerivAt_aeval _ _
  have hid : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hA : HasDerivAt (fun y : ℝ => aeval y (derivative (hermite n)) - y / 2 * aeval y (hermite n))
      (aeval x (derivative (derivative (hermite n)))
        - (1 / 2 * aeval x (hermite n) + x / 2 * aeval x (derivative (hermite n)))) x :=
    h1.sub (hid.mul h0)
  have h2 := hasDerivAt_gauss x
  have hmul := hA.mul h2
  refine hmul.congr_deriv ?_
  simp only [hermiteGauss, He, hode x]
  ring

/-! ### The physical Landau problem -/

/-- The magnetic length scale `sqrt (ħ / (2 m ω_c))` appearing in the Landau eigenfunctions. -/
