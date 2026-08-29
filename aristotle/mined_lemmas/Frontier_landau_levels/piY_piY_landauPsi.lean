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

theorem piY_piY_landauPsi (x y : ℝ) :
    piY hbar q B (piY hbar q B (landauPsi hbar q B k n)) x y
      = ((hbar * k - q * B * x : ℝ) : ℂ) ^ 2 * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
        * ((phiR hbar q B k n x : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => piY hbar q B (landauPsi hbar q B k n) x t)
      = fun t : ℝ => ((hbar * k - q * B * x : ℝ) : ℂ)
          * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))
          * ((phiR hbar q B k n x : ℝ) : ℂ) := funext fun t => piY_landauPsi x t
  have hd : deriv (fun t : ℝ => piY hbar q B (landauPsi hbar q B k n) x t) y
      = ((hbar * k - q * B * x : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * (Complex.I * (k : ℂ)))
        * ((phiR hbar q B k n x : ℝ) : ℂ) := by
    rw [hfun]
    exact (((hasDerivAt_cexp_lin k y).const_mul ((hbar * k - q * B * x : ℝ) : ℂ)).mul_const
      ((phiR hbar q B k n x : ℝ) : ℂ)).deriv
  rw [piY_apply, hd, piY_landauPsi]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-((hbar : ℂ) * (k : ℂ) * ((hbar : ℂ) * (k : ℂ)
    - (q : ℂ) * (B : ℂ) * (x : ℂ)) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
    * ((phiR hbar q B k n x : ℝ) : ℂ))) * hI

/-! ### The scalar identity -/

