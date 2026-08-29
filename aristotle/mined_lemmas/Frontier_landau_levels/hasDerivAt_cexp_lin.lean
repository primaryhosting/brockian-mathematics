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

theorem hasDerivAt_cexp_lin (k y : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)))
      (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * (Complex.I * (k : ℂ))) y := by
  have h0 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 y := (hasDerivAt_id y).ofReal_comp
  simpa using (h0.const_mul (Complex.I * (k : ℂ))).cexp

