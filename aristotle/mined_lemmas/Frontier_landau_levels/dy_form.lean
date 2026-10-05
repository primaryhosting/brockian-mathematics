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

theorem dy_form (f : ℝ → ℝ → ℂ) (F : ℝ → ℂ) (k : ℝ)
    (hf : ∀ a b : ℝ, f a b = Complex.exp (Complex.I * k * b) * F a) (x y : ℝ) :
    dy f x y = Complex.I * k * (Complex.exp (Complex.I * k * y) * F x) := by
  have hfun : (fun t : ℝ => f x t)
      = fun t : ℝ => Complex.exp (Complex.I * k * t) * F x := by
    funext t; exact hf x t
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * k * (t : ℂ)) (Complex.I * k) y := by
    simpa using h0.const_mul (Complex.I * (k : ℂ))
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * k * (t : ℂ)))
      (Complex.exp (Complex.I * k * (y : ℂ)) * (Complex.I * k)) y := h1.cexp
  have h3 := h2.mul_const (F x)
  rw [dy, hfun, h3.deriv]
  ring

/-- The algebraic identity behind the Landau spectrum: with magnetic length `s`
satisfying `s² = ℏ/(2c)` (`c = qB`) and guiding centre `x₀ = ℏk/c`, the potential terms
combine to the constant `2m · ℏ(c/m)(n + 1/2)`. -/
