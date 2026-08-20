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

theorem hermiteQ_deriv (n : ℕ) :
    derivative (hermiteQ n) - X * hermiteQ n = (X ^ 2 - (2 * (n : ℝ[X]) + 1)) * hermiteP n := by
  have h := hermiteP_ode n
  simp only [hermiteQ, derivative_sub, derivative_mul, derivative_X, one_mul]
  linear_combination h

/-- The second derivative of the Hermite function satisfies
`u_n'' (t) = (t² - (2n+1)) u_n (t)`, i.e. `-u'' + t² u = (2n+1) u`. -/
