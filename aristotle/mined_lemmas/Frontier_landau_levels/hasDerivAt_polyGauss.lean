/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

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

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/

theorem hasDerivAt_polyGauss (q : ℝ[X]) (a b x0 t : ℝ) :
    HasDerivAt (polyGauss q a b x0)
      ((a * (derivative q).eval (a * (t - x0)) - 2 * b * (t - x0) * q.eval (a * (t - x0)))
        * Real.exp (-(b * (t - x0) ^ 2))) t := by
  have h1 : HasDerivAt (fun s : ℝ => a * (s - x0)) a t := by
    simpa using ((hasDerivAt_id t).sub_const x0).const_mul a
  have h2 : HasDerivAt (fun s : ℝ => q.eval (a * (s - x0)))
      ((derivative q).eval (a * (t - x0)) * a) t := by
    simpa [Function.comp_def] using HasDerivAt.comp t (q.hasDerivAt (a * (t - x0))) h1
  have h3 : HasDerivAt (fun s : ℝ => -(b * (s - x0) ^ 2)) (-(b * (2 * (t - x0)))) t := by
    have := (((hasDerivAt_id t).sub_const x0).pow 2).const_mul b
    simpa using this.neg
  have h5 := h2.mul h3.exp
  unfold polyGauss
  convert h5 using 1
  ring

