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

theorem gfun_hermiteQ_deriv (n : ℕ) (s : ℝ) :
    gfun (derivative (hermiteQ n) - X * hermiteQ n) s = (s ^ 2 - (2 * n + 1)) * oscFun n s := by
  rw [hermiteQ_deriv]
  simp [gfun, oscFun]
  ring

/-- The oscillator eigenfunctions are not identically zero. -/
