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

theorem hasDerivAt_cexp_lin (k y : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * k * s))
      (Complex.exp (Complex.I * k * y) * (Complex.I * k)) y := by
  have h0 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) (1 : ℂ) y := (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * (k : ℂ) * (s : ℂ)) (Complex.I * k) y := by
    simpa using h0.const_mul (Complex.I * (k : ℂ))
  simpa using h1.cexp

/-- On a separated state `exp (i k y) f(x)`, the operator `π_y` acts as multiplication by
`ℏk - qBx`. -/
