import Mathlib

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

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem hasDerivAt_gfun (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (gfun p) (gfun (derivative p - X * p) t) t := by
  have h1 : HasDerivAt (fun s : ℝ => p.eval s) ((derivative p).eval t) t := p.hasDerivAt t
  have h2 : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-t) t :=
    ((hasDerivAt_pow 2 t).neg.div_const 2).congr_deriv (by push_cast; ring)
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2)) (Real.exp (-t ^ 2 / 2) * (-t)) t := h2.exp
  have h4 : HasDerivAt (gfun p)
      (eval t (derivative p) * Real.exp (-t ^ 2 / 2)
        + eval t p * (Real.exp (-t ^ 2 / 2) * -t)) t := h1.mul h3
  refine h4.congr_deriv ?_
  simp [gfun]; ring

/-- Derivative of `t ↦ gfun p (c * (t - d))`. -/
