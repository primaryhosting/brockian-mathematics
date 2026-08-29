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

namespace Frontier

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/

theorem R_R_hermiteR (n : ℕ) :
    R (R (hermiteR n)) = X ^ 2 * hermiteR n - (4 * (n : ℝ[X]) + 2) * hermiteR n := by
  simp only [R, derivative_sub, derivative_mul, derivative_X, derivative_ofNat, hermiteR_ode n]
  ring

/-! ## The oscillator profile `χ_n` -/

/-- The `n`-th (unnormalised) harmonic-oscillator profile `χ_n(x) = He_n(x) e^{-x²/4}`. -/
