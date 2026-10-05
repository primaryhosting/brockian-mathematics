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

theorem deriv_x_landauPsi (hhbar : 0 < hbar) (hqB : 0 < q * B) (x y : ℝ) :
    deriv (fun t : ℝ => landauPsi hbar q B k n t y) x
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((dphiR hbar q B k n x : ℝ) : ℂ) :=
  (((hasDerivAt_phiR (k := k) (n := n) hhbar hqB x).ofReal_comp).const_mul
    (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)))).deriv

