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

theorem hermiteP_ode (n : ℕ) :
    derivative (derivative (hermiteP n)) - 2 * X * derivative (hermiteP n)
      + 2 * (n : ℝ[X]) * hermiteP n = 0 := (hermiteP_ode_and_derivative n).1

/-- `H_n` has degree `n` with leading coefficient `2^n`. -/
