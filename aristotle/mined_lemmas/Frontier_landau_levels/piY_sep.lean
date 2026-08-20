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

theorem piY_sep (hbar q B k : ℝ) (f : ℝ → ℝ) :
    piY hbar q B (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ))
      = fun x y : ℝ =>
        Complex.exp (Complex.I * k * y) * (((hbar * k - q * B * x) * f x : ℝ) : ℂ) := by
  funext x y
  have hd : deriv (fun s : ℝ => Complex.exp (Complex.I * k * s) * (f x : ℂ)) y
      = Complex.exp (Complex.I * k * y) * (Complex.I * k) * (f x : ℂ) :=
    ((hasDerivAt_cexp_lin k y).mul_const (f x : ℂ)).deriv
  simp only [piY, hd]
  push_cast
  linear_combination (-(hbar : ℂ) * k * Complex.exp (Complex.I * k * y) * (f x : ℂ)) * Complex.I_sq

/-- On a separated state `exp (i k y) f(x)`, the operator `π_x` differentiates the `x` factor. -/
