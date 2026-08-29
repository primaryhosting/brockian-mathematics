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

noncomputable section

open Polynomial

/-! ## Probabilists' Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, with real coefficients. -/

theorem dx_form (f : ℝ → ℝ → ℂ) (c : ℂ) (g g' : ℝ → ℝ) (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (k x0 : ℝ)
    (hf : ∀ a b : ℝ, f a b = c * Complex.exp (Complex.I * k * b) * ((g (a - x0) : ℝ) : ℂ))
    (x y : ℝ) :
    dx f x y = c * Complex.exp (Complex.I * k * y) * ((g' (x - x0) : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => f t y)
      = fun t : ℝ => c * Complex.exp (Complex.I * k * y) * ((g (t - x0) : ℝ) : ℂ) := by
    funext t; exact hf t y
  have hshift : HasDerivAt (fun t : ℝ => g (t - x0)) (g' (x - x0)) x := by
    simpa using (hg (x - x0)).comp x ((hasDerivAt_id x).sub_const x0)
  have hC : HasDerivAt (fun t : ℝ => ((g (t - x0) : ℝ) : ℂ)) ((g' (x - x0) : ℝ) : ℂ) x :=
    hshift.ofReal_comp
  have hmul := hC.const_mul (c * Complex.exp (Complex.I * k * y))
  rw [dx, hfun, hmul.deriv]

/-- `y`-derivative of a function of the product form `e^{iky} * F x`. -/
