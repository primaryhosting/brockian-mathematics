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

theorem hasDerivAt_F (P : ℝ[X]) (x : ℝ) : HasDerivAt (F P) ((1 / 2) * F (R P) x) x := by
  have h1 : HasDerivAt (fun x : ℝ => P.eval x) (P.derivative.eval x) x := P.hasDerivAt x
  have hg : HasDerivAt (fun x : ℝ => -x ^ 2 / 4) (-x / 2) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const 4
    convert h using 1
    push_cast; ring
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 4))
      (Real.exp (-x ^ 2 / 4) * (-x / 2)) x := hg.exp
  have h3 := h1.mul h2
  convert h3 using 1
  simp only [F, R, eval_sub, eval_mul, eval_X, eval_ofNat]
  ring

